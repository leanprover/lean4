// Lean compiler output
// Module: Lean.Expr
// Imports: public import Init.Data.Hashable public import Init.System.IO public import Lean.Data.LBool public import Lean.Level import Init.Omega
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
uint32_t lean_uint64_to_uint32(uint64_t);
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
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint64_to_uint8(uint64_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_uint32_mix_hash(uint32_t, uint32_t);
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
uint64_t lean_uint32_to_uint64(uint32_t);
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
LEAN_EXPORT uint32_t l_Lean_Expr_Data_hash(uint64_t);
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
uint64_t lean_expr_mk_data(uint32_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_expr_mk_app_data(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint32_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint32_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " (hasLevelMVar := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " (hasExprMVar := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__3 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " (hasFVar := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__4 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " (approxDepth := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__5 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Expr.mkData "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__6 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " (looseBVarRange := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__7 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__7_value;
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
uint8_t lean_expr_eqv_budgeted(lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_eqvBudgeted___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal_budgeted(lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_equalBudgeted___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Expr_isBoolFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Expr_isBoolFalse___closed__1 = (const lean_object*)&l_Lean_Expr_isBoolFalse___closed__1_value;
static const lean_ctor_object l_Lean_Expr_isBoolFalse___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isBoolFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_isBoolFalse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isBoolFalse___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_isBoolFalse___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Expr_isBoolFalse___closed__2 = (const lean_object*)&l_Lean_Expr_isBoolFalse___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object*);
static const lean_ctor_object l_Lean_Expr_isBoolTrue___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isBoolFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_isBoolTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isBoolTrue___closed__0_value_aux_0),((lean_object*)&l_Lean_instReprData__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Expr_isBoolTrue___closed__0 = (const lean_object*)&l_Lean_Expr_isBoolTrue___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_int_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Expr_int_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_int_x3f___closed__0_value;
static const lean_string_object l_Lean_Expr_int_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Expr_int_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_int_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Expr_int_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_int_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Expr_int_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_int_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_int_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Expr_int_x3f___closed__2 = (const lean_object*)&l_Lean_Expr_int_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f___boxed(lean_object*);
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
static const lean_string_object l_Lean_mkNatDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_mkNatDiv___closed__0 = (const lean_object*)&l_Lean_mkNatDiv___closed__0_value;
static const lean_string_object l_Lean_mkNatDiv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_mkNatDiv___closed__1 = (const lean_object*)&l_Lean_mkNatDiv___closed__1_value;
static const lean_ctor_object l_Lean_mkNatDiv___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkNatDiv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_mkNatDiv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkNatDiv___closed__2_value_aux_0),((lean_object*)&l_Lean_mkNatDiv___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_mkNatDiv___closed__2 = (const lean_object*)&l_Lean_mkNatDiv___closed__2_value;
static lean_once_cell_t l_Lean_mkNatDiv___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkNatDiv___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkNatDiv(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkNatMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Lean_mkNatMod___closed__0 = (const lean_object*)&l_Lean_mkNatMod___closed__0_value;
static const lean_string_object l_Lean_mkNatMod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Lean_mkNatMod___closed__1 = (const lean_object*)&l_Lean_mkNatMod___closed__1_value;
static const lean_ctor_object l_Lean_mkNatMod___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkNatMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Lean_mkNatMod___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkNatMod___closed__2_value_aux_0),((lean_object*)&l_Lean_mkNatMod___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Lean_mkNatMod___closed__2 = (const lean_object*)&l_Lean_mkNatMod___closed__2_value;
static lean_once_cell_t l_Lean_mkNatMod___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkNatMod___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkNatMod(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intDivFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intDivFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intDivFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intModFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intModFn___closed__0;
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
LEAN_EXPORT uint32_t l_Lean_Expr_Data_hash(uint64_t v_c_354_){
_start:
{
uint32_t v___x_355_; 
v___x_355_ = lean_uint64_to_uint32(v_c_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* v_c_356_){
_start:
{
uint64_t v_c_boxed_357_; uint32_t v_res_358_; lean_object* v_r_359_; 
v_c_boxed_357_ = lean_unbox_uint64(v_c_356_);
lean_dec_ref(v_c_356_);
v_res_358_ = l_Lean_Expr_Data_hash(v_c_boxed_357_);
v_r_359_ = lean_box_uint32(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t v_c_362_){
_start:
{
uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v___x_366_; uint8_t v___x_367_; 
v___x_363_ = 32ULL;
v___x_364_ = lean_uint64_shift_right(v_c_362_, v___x_363_);
v___x_365_ = 255ULL;
v___x_366_ = lean_uint64_land(v___x_364_, v___x_365_);
v___x_367_ = lean_uint64_to_uint8(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* v_c_368_){
_start:
{
uint64_t v_c_boxed_369_; uint8_t v_res_370_; lean_object* v_r_371_; 
v_c_boxed_369_ = lean_unbox_uint64(v_c_368_);
lean_dec_ref(v_c_368_);
v_res_370_ = l_Lean_Expr_Data_approxDepth(v_c_boxed_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t v_c_372_){
_start:
{
uint64_t v___x_373_; uint64_t v___x_374_; uint32_t v___x_375_; 
v___x_373_ = 44ULL;
v___x_374_ = lean_uint64_shift_right(v_c_372_, v___x_373_);
v___x_375_ = lean_uint64_to_uint32(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* v_c_376_){
_start:
{
uint64_t v_c_boxed_377_; uint32_t v_res_378_; lean_object* v_r_379_; 
v_c_boxed_377_ = lean_unbox_uint64(v_c_376_);
lean_dec_ref(v_c_376_);
v_res_378_ = l_Lean_Expr_Data_looseBVarRange(v_c_boxed_377_);
v_r_379_ = lean_box_uint32(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t v_c_380_){
_start:
{
uint64_t v___x_381_; uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint8_t v___x_385_; 
v___x_381_ = 40ULL;
v___x_382_ = lean_uint64_shift_right(v_c_380_, v___x_381_);
v___x_383_ = 1ULL;
v___x_384_ = lean_uint64_land(v___x_382_, v___x_383_);
v___x_385_ = lean_uint64_dec_eq(v___x_384_, v___x_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* v_c_386_){
_start:
{
uint64_t v_c_boxed_387_; uint8_t v_res_388_; lean_object* v_r_389_; 
v_c_boxed_387_ = lean_unbox_uint64(v_c_386_);
lean_dec_ref(v_c_386_);
v_res_388_ = l_Lean_Expr_Data_hasFVar(v_c_boxed_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t v_c_390_){
_start:
{
uint64_t v___x_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint8_t v___x_395_; 
v___x_391_ = 41ULL;
v___x_392_ = lean_uint64_shift_right(v_c_390_, v___x_391_);
v___x_393_ = 1ULL;
v___x_394_ = lean_uint64_land(v___x_392_, v___x_393_);
v___x_395_ = lean_uint64_dec_eq(v___x_394_, v___x_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* v_c_396_){
_start:
{
uint64_t v_c_boxed_397_; uint8_t v_res_398_; lean_object* v_r_399_; 
v_c_boxed_397_ = lean_unbox_uint64(v_c_396_);
lean_dec_ref(v_c_396_);
v_res_398_ = l_Lean_Expr_Data_hasExprMVar(v_c_boxed_397_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t v_c_400_){
_start:
{
uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint8_t v___x_405_; 
v___x_401_ = 42ULL;
v___x_402_ = lean_uint64_shift_right(v_c_400_, v___x_401_);
v___x_403_ = 1ULL;
v___x_404_ = lean_uint64_land(v___x_402_, v___x_403_);
v___x_405_ = lean_uint64_dec_eq(v___x_404_, v___x_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* v_c_406_){
_start:
{
uint64_t v_c_boxed_407_; uint8_t v_res_408_; lean_object* v_r_409_; 
v_c_boxed_407_ = lean_unbox_uint64(v_c_406_);
lean_dec_ref(v_c_406_);
v_res_408_ = l_Lean_Expr_Data_hasLevelMVar(v_c_boxed_407_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t v_c_410_){
_start:
{
uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint8_t v___x_415_; 
v___x_411_ = 43ULL;
v___x_412_ = lean_uint64_shift_right(v_c_410_, v___x_411_);
v___x_413_ = 1ULL;
v___x_414_ = lean_uint64_land(v___x_412_, v___x_413_);
v___x_415_ = lean_uint64_dec_eq(v___x_414_, v___x_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* v_c_416_){
_start:
{
uint64_t v_c_boxed_417_; uint8_t v_res_418_; lean_object* v_r_419_; 
v_c_boxed_417_ = lean_unbox_uint64(v_c_416_);
lean_dec_ref(v_c_416_);
v_res_418_ = l_Lean_Expr_Data_hasLevelParam(v_c_boxed_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_421_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_422_; uint64_t v_res_423_; lean_object* v_r_424_; 
v_a_00___x40___internal___hyg_1__boxed_422_ = lean_unbox(v_a_00___x40___internal___hyg_421_);
v_res_423_ = lean_uint8_to_uint64(v_a_00___x40___internal___hyg_1__boxed_422_);
v_r_424_ = lean_box_uint64(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* v_h_432_, lean_object* v_looseBVarRange_433_, lean_object* v_approxDepth_434_, lean_object* v_hasFVar_435_, lean_object* v_hasExprMVar_436_, lean_object* v_hasLevelMVar_437_, lean_object* v_hasLevelParam_438_){
_start:
{
uint32_t v_h_boxed_439_; uint32_t v_approxDepth_boxed_440_; uint8_t v_hasFVar_boxed_441_; uint8_t v_hasExprMVar_boxed_442_; uint8_t v_hasLevelMVar_boxed_443_; uint8_t v_hasLevelParam_boxed_444_; uint64_t v_res_445_; lean_object* v_r_446_; 
v_h_boxed_439_ = lean_unbox_uint32(v_h_432_);
lean_dec(v_h_432_);
v_approxDepth_boxed_440_ = lean_unbox_uint32(v_approxDepth_434_);
lean_dec(v_approxDepth_434_);
v_hasFVar_boxed_441_ = lean_unbox(v_hasFVar_435_);
v_hasExprMVar_boxed_442_ = lean_unbox(v_hasExprMVar_436_);
v_hasLevelMVar_boxed_443_ = lean_unbox(v_hasLevelMVar_437_);
v_hasLevelParam_boxed_444_ = lean_unbox(v_hasLevelParam_438_);
v_res_445_ = lean_expr_mk_data(v_h_boxed_439_, v_looseBVarRange_433_, v_approxDepth_boxed_440_, v_hasFVar_boxed_441_, v_hasExprMVar_boxed_442_, v_hasLevelMVar_boxed_443_, v_hasLevelParam_boxed_444_);
v_r_446_ = lean_box_uint64(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* v_fData_449_, lean_object* v_aData_450_){
_start:
{
uint64_t v_fData_boxed_451_; uint64_t v_aData_boxed_452_; uint64_t v_res_453_; lean_object* v_r_454_; 
v_fData_boxed_451_ = lean_unbox_uint64(v_fData_449_);
lean_dec_ref(v_fData_449_);
v_aData_boxed_452_ = lean_unbox_uint64(v_aData_450_);
lean_dec_ref(v_aData_450_);
v_res_453_ = lean_expr_mk_app_data(v_fData_boxed_451_, v_aData_boxed_452_);
v_r_454_ = lean_box_uint64(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint32_t v_h_455_, lean_object* v_looseBVarRange_456_, uint32_t v_approxDepth_457_, uint8_t v_hasFVar_458_, uint8_t v_hasExprMVar_459_, uint8_t v_hasLevelMVar_460_, uint8_t v_hasLevelParam_461_){
_start:
{
uint64_t v___x_462_; 
v___x_462_ = lean_expr_mk_data(v_h_455_, v_looseBVarRange_456_, v_approxDepth_457_, v_hasFVar_458_, v_hasExprMVar_459_, v_hasLevelMVar_460_, v_hasLevelParam_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* v_h_463_, lean_object* v_looseBVarRange_464_, lean_object* v_approxDepth_465_, lean_object* v_hasFVar_466_, lean_object* v_hasExprMVar_467_, lean_object* v_hasLevelMVar_468_, lean_object* v_hasLevelParam_469_){
_start:
{
uint32_t v_h_boxed_470_; uint32_t v_approxDepth_boxed_471_; uint8_t v_hasFVar_boxed_472_; uint8_t v_hasExprMVar_boxed_473_; uint8_t v_hasLevelMVar_boxed_474_; uint8_t v_hasLevelParam_boxed_475_; uint64_t v_res_476_; lean_object* v_r_477_; 
v_h_boxed_470_ = lean_unbox_uint32(v_h_463_);
lean_dec(v_h_463_);
v_approxDepth_boxed_471_ = lean_unbox_uint32(v_approxDepth_465_);
lean_dec(v_approxDepth_465_);
v_hasFVar_boxed_472_ = lean_unbox(v_hasFVar_466_);
v_hasExprMVar_boxed_473_ = lean_unbox(v_hasExprMVar_467_);
v_hasLevelMVar_boxed_474_ = lean_unbox(v_hasLevelMVar_468_);
v_hasLevelParam_boxed_475_ = lean_unbox(v_hasLevelParam_469_);
v_res_476_ = l_Lean_Expr_mkDataForBinder(v_h_boxed_470_, v_looseBVarRange_464_, v_approxDepth_boxed_471_, v_hasFVar_boxed_472_, v_hasExprMVar_boxed_473_, v_hasLevelMVar_boxed_474_, v_hasLevelParam_boxed_475_);
v_r_477_ = lean_box_uint64(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint32_t v_h_478_, lean_object* v_looseBVarRange_479_, uint32_t v_approxDepth_480_, uint8_t v_hasFVar_481_, uint8_t v_hasExprMVar_482_, uint8_t v_hasLevelMVar_483_, uint8_t v_hasLevelParam_484_){
_start:
{
uint64_t v___x_485_; 
v___x_485_ = lean_expr_mk_data(v_h_478_, v_looseBVarRange_479_, v_approxDepth_480_, v_hasFVar_481_, v_hasExprMVar_482_, v_hasLevelMVar_483_, v_hasLevelParam_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* v_h_486_, lean_object* v_looseBVarRange_487_, lean_object* v_approxDepth_488_, lean_object* v_hasFVar_489_, lean_object* v_hasExprMVar_490_, lean_object* v_hasLevelMVar_491_, lean_object* v_hasLevelParam_492_){
_start:
{
uint32_t v_h_boxed_493_; uint32_t v_approxDepth_boxed_494_; uint8_t v_hasFVar_boxed_495_; uint8_t v_hasExprMVar_boxed_496_; uint8_t v_hasLevelMVar_boxed_497_; uint8_t v_hasLevelParam_boxed_498_; uint64_t v_res_499_; lean_object* v_r_500_; 
v_h_boxed_493_ = lean_unbox_uint32(v_h_486_);
lean_dec(v_h_486_);
v_approxDepth_boxed_494_ = lean_unbox_uint32(v_approxDepth_488_);
lean_dec(v_approxDepth_488_);
v_hasFVar_boxed_495_ = lean_unbox(v_hasFVar_489_);
v_hasExprMVar_boxed_496_ = lean_unbox(v_hasExprMVar_490_);
v_hasLevelMVar_boxed_497_ = lean_unbox(v_hasLevelMVar_491_);
v_hasLevelParam_boxed_498_ = lean_unbox(v_hasLevelParam_492_);
v_res_499_ = l_Lean_Expr_mkDataForLet(v_h_boxed_493_, v_looseBVarRange_487_, v_approxDepth_boxed_494_, v_hasFVar_boxed_495_, v_hasExprMVar_boxed_496_, v_hasLevelMVar_boxed_497_, v_hasLevelParam_boxed_498_);
v_r_500_ = lean_box_uint64(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t v_v_509_, lean_object* v_prec_510_){
_start:
{
lean_object* v_r_512_; lean_object* v_r_516_; lean_object* v_r_525_; lean_object* v_r_534_; lean_object* v_r_543_; lean_object* v___x_554_; uint32_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_r_558_; uint32_t v___x_559_; uint32_t v___x_560_; uint8_t v___x_561_; 
v___x_554_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__6));
v___x_555_ = lean_uint64_to_uint32(v_v_509_);
v___x_556_ = lean_uint32_to_nat(v___x_555_);
v___x_557_ = l_Nat_reprFast(v___x_556_);
v_r_558_ = lean_string_append(v___x_554_, v___x_557_);
lean_dec_ref(v___x_557_);
v___x_559_ = l_Lean_Expr_Data_looseBVarRange(v_v_509_);
v___x_560_ = 0;
v___x_561_ = lean_uint32_dec_eq(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v_r_568_; 
v___x_562_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__7));
v___x_563_ = lean_string_append(v_r_558_, v___x_562_);
v___x_564_ = lean_uint32_to_nat(v___x_559_);
v___x_565_ = l_Nat_reprFast(v___x_564_);
v___x_566_ = lean_string_append(v___x_563_, v___x_565_);
lean_dec_ref(v___x_565_);
v___x_567_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_568_ = lean_string_append(v___x_566_, v___x_567_);
v_r_543_ = v_r_568_;
goto v___jp_542_;
}
else
{
v_r_543_ = v_r_558_;
goto v___jp_542_;
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_513_, 0, v_r_512_);
v___x_514_ = l_Repr_addAppParen(v___x_513_, v_prec_510_);
return v___x_514_;
}
v___jp_515_:
{
uint8_t v___x_517_; 
v___x_517_ = l_Lean_Expr_Data_hasLevelMVar(v_v_509_);
if (v___x_517_ == 0)
{
v_r_512_ = v_r_516_;
goto v___jp_511_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_r_523_; 
v___x_518_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v___x_519_ = lean_string_append(v_r_516_, v___x_518_);
v___x_520_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
v___x_522_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_523_ = lean_string_append(v___x_521_, v___x_522_);
v_r_512_ = v_r_523_;
goto v___jp_511_;
}
}
v___jp_524_:
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Expr_Data_hasExprMVar(v_v_509_);
if (v___x_526_ == 0)
{
v_r_516_ = v_r_525_;
goto v___jp_515_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_r_532_; 
v___x_527_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___x_528_ = lean_string_append(v_r_525_, v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_530_ = lean_string_append(v___x_528_, v___x_529_);
v___x_531_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_532_ = lean_string_append(v___x_530_, v___x_531_);
v_r_516_ = v_r_532_;
goto v___jp_515_;
}
}
v___jp_533_:
{
uint8_t v___x_535_; 
v___x_535_ = l_Lean_Expr_Data_hasFVar(v_v_509_);
if (v___x_535_ == 0)
{
v_r_525_ = v_r_534_;
goto v___jp_524_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_r_541_; 
v___x_536_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__4));
v___x_537_ = lean_string_append(v_r_534_, v___x_536_);
v___x_538_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_539_ = lean_string_append(v___x_537_, v___x_538_);
v___x_540_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_541_ = lean_string_append(v___x_539_, v___x_540_);
v_r_525_ = v_r_541_;
goto v___jp_524_;
}
}
v___jp_542_:
{
uint8_t v___x_544_; uint8_t v___x_545_; uint8_t v___x_546_; 
v___x_544_ = l_Lean_Expr_Data_approxDepth(v_v_509_);
v___x_545_ = 0;
v___x_546_ = lean_uint8_dec_eq(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_r_553_; 
v___x_547_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__5));
v___x_548_ = lean_string_append(v_r_543_, v___x_547_);
v___x_549_ = lean_uint8_to_nat(v___x_544_);
v___x_550_ = l_Nat_reprFast(v___x_549_);
v___x_551_ = lean_string_append(v___x_548_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_553_ = lean_string_append(v___x_551_, v___x_552_);
v_r_534_ = v_r_553_;
goto v___jp_533_;
}
else
{
v_r_534_ = v_r_543_;
goto v___jp_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* v_v_569_, lean_object* v_prec_570_){
_start:
{
uint64_t v_v_boxed_571_; lean_object* v_res_572_; 
v_v_boxed_571_ = lean_unbox_uint64(v_v_569_);
lean_dec_ref(v_v_569_);
v_res_572_ = l_Lean_instReprData__1___lam__0(v_v_boxed_571_, v_prec_570_);
lean_dec(v_prec_570_);
return v_res_572_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId_default(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_box(0);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_box(0);
return v___x_576_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = lean_name_eq(v_x_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
uint8_t v_res_582_; lean_object* v_r_583_; 
v_res_582_ = l_Lean_instBEqFVarId_beq(v_x_580_, v_x_581_);
lean_dec(v_x_581_);
lean_dec(v_x_580_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_586_){
_start:
{
uint64_t v___x_587_; 
v___x_587_ = 0ULL;
if (lean_obj_tag(v_x_586_) == 0)
{
uint64_t v___x_588_; 
v___x_588_ = 8934034000889494153ULL;
return v___x_588_;
}
else
{
uint64_t v_hash_589_; uint64_t v___x_590_; 
v_hash_589_ = lean_ctor_get_uint64(v_x_586_, sizeof(void*)*2);
v___x_590_ = lean_uint64_mix_hash(v___x_587_, v_hash_589_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_591_){
_start:
{
uint64_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_Lean_instHashableFVarId_hash(v_x_591_);
lean_dec(v_x_591_);
v_r_593_ = lean_box_uint64(v_res_592_);
return v_r_593_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = lean_box(1);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(1);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(1);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet(void){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_box(1);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object* v_e_603_){
_start:
{
lean_object* v___f_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___f_604_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_605_ = lean_box(1);
lean_inc(v_e_603_);
v___x_606_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_604_, v_e_603_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_box(0);
v___x_608_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_604_, v_e_603_, v___x_607_, v___x_605_);
return v___x_608_;
}
else
{
lean_dec(v_e_603_);
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object* v_k_609_, lean_object* v_v_610_, lean_object* v_t_611_){
_start:
{
if (lean_obj_tag(v_t_611_) == 0)
{
lean_object* v_size_612_; lean_object* v_k_613_; lean_object* v_v_614_; lean_object* v_l_615_; lean_object* v_r_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_896_; 
v_size_612_ = lean_ctor_get(v_t_611_, 0);
v_k_613_ = lean_ctor_get(v_t_611_, 1);
v_v_614_ = lean_ctor_get(v_t_611_, 2);
v_l_615_ = lean_ctor_get(v_t_611_, 3);
v_r_616_ = lean_ctor_get(v_t_611_, 4);
v_isSharedCheck_896_ = !lean_is_exclusive(v_t_611_);
if (v_isSharedCheck_896_ == 0)
{
v___x_618_ = v_t_611_;
v_isShared_619_ = v_isSharedCheck_896_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_r_616_);
lean_inc(v_l_615_);
lean_inc(v_v_614_);
lean_inc(v_k_613_);
lean_inc(v_size_612_);
lean_dec(v_t_611_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_896_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint8_t v___x_620_; 
v___x_620_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_609_, v_k_613_);
switch(v___x_620_)
{
case 0:
{
lean_object* v_impl_621_; lean_object* v___x_622_; 
lean_dec(v_size_612_);
v_impl_621_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_609_, v_v_610_, v_l_615_);
v___x_622_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_616_) == 0)
{
lean_object* v_size_623_; lean_object* v_size_624_; lean_object* v_k_625_; lean_object* v_v_626_; lean_object* v_l_627_; lean_object* v_r_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_size_623_ = lean_ctor_get(v_r_616_, 0);
v_size_624_ = lean_ctor_get(v_impl_621_, 0);
v_k_625_ = lean_ctor_get(v_impl_621_, 1);
v_v_626_ = lean_ctor_get(v_impl_621_, 2);
v_l_627_ = lean_ctor_get(v_impl_621_, 3);
v_r_628_ = lean_ctor_get(v_impl_621_, 4);
lean_inc(v_r_628_);
v___x_629_ = lean_unsigned_to_nat(3u);
v___x_630_ = lean_nat_mul(v___x_629_, v_size_623_);
v___x_631_ = lean_nat_dec_lt(v___x_630_, v_size_624_);
lean_dec(v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
lean_dec(v_r_628_);
v___x_632_ = lean_nat_add(v___x_622_, v_size_624_);
v___x_633_ = lean_nat_add(v___x_632_, v_size_623_);
lean_dec(v___x_632_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 3, v_impl_621_);
lean_ctor_set(v___x_618_, 0, v___x_633_);
v___x_635_ = v___x_618_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_impl_621_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_r_616_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
else
{
lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_702_; 
lean_inc(v_l_627_);
lean_inc(v_v_626_);
lean_inc(v_k_625_);
lean_inc(v_size_624_);
v_isSharedCheck_702_ = !lean_is_exclusive(v_impl_621_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; lean_object* v_unused_704_; lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; 
v_unused_703_ = lean_ctor_get(v_impl_621_, 4);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v_impl_621_, 3);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v_impl_621_, 2);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v_impl_621_, 1);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_impl_621_, 0);
lean_dec(v_unused_707_);
v___x_638_ = v_impl_621_;
v_isShared_639_ = v_isSharedCheck_702_;
goto v_resetjp_637_;
}
else
{
lean_dec(v_impl_621_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_702_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_size_640_; lean_object* v_size_641_; lean_object* v_k_642_; lean_object* v_v_643_; lean_object* v_l_644_; lean_object* v_r_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_size_640_ = lean_ctor_get(v_l_627_, 0);
v_size_641_ = lean_ctor_get(v_r_628_, 0);
v_k_642_ = lean_ctor_get(v_r_628_, 1);
v_v_643_ = lean_ctor_get(v_r_628_, 2);
v_l_644_ = lean_ctor_get(v_r_628_, 3);
v_r_645_ = lean_ctor_get(v_r_628_, 4);
v___x_646_ = lean_unsigned_to_nat(2u);
v___x_647_ = lean_nat_mul(v___x_646_, v_size_640_);
v___x_648_ = lean_nat_dec_lt(v_size_641_, v___x_647_);
lean_dec(v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_677_; 
lean_inc(v_r_645_);
lean_inc(v_l_644_);
lean_inc(v_v_643_);
lean_inc(v_k_642_);
v_isSharedCheck_677_ = !lean_is_exclusive(v_r_628_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; lean_object* v_unused_679_; lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; 
v_unused_678_ = lean_ctor_get(v_r_628_, 4);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_r_628_, 3);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_r_628_, 2);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_r_628_, 1);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_r_628_, 0);
lean_dec(v_unused_682_);
v___x_650_ = v_r_628_;
v_isShared_651_ = v_isSharedCheck_677_;
goto v_resetjp_649_;
}
else
{
lean_dec(v_r_628_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_677_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___x_665_; lean_object* v___y_667_; 
v___x_652_ = lean_nat_add(v___x_622_, v_size_624_);
lean_dec(v_size_624_);
v___x_653_ = lean_nat_add(v___x_652_, v_size_623_);
lean_dec(v___x_652_);
v___x_665_ = lean_nat_add(v___x_622_, v_size_640_);
if (lean_obj_tag(v_l_644_) == 0)
{
lean_object* v_size_675_; 
v_size_675_ = lean_ctor_get(v_l_644_, 0);
lean_inc(v_size_675_);
v___y_667_ = v_size_675_;
goto v___jp_666_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___y_667_ = v___x_676_;
goto v___jp_666_;
}
v___jp_654_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = lean_nat_add(v___y_655_, v___y_657_);
lean_dec(v___y_657_);
lean_dec(v___y_655_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 4, v_r_616_);
lean_ctor_set(v___x_650_, 3, v_r_645_);
lean_ctor_set(v___x_650_, 2, v_v_614_);
lean_ctor_set(v___x_650_, 1, v_k_613_);
lean_ctor_set(v___x_650_, 0, v___x_658_);
v___x_660_ = v___x_650_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v_r_645_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v_r_616_);
v___x_660_ = v_reuseFailAlloc_664_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_662_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v___x_660_);
lean_ctor_set(v___x_638_, 3, v___y_656_);
lean_ctor_set(v___x_638_, 2, v_v_643_);
lean_ctor_set(v___x_638_, 1, v_k_642_);
lean_ctor_set(v___x_638_, 0, v___x_653_);
v___x_662_ = v___x_638_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_663_, 3, v___y_656_);
lean_ctor_set(v_reuseFailAlloc_663_, 4, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
v___jp_666_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = lean_nat_add(v___x_665_, v___y_667_);
lean_dec(v___y_667_);
lean_dec(v___x_665_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_l_644_);
lean_ctor_set(v___x_618_, 3, v_l_627_);
lean_ctor_set(v___x_618_, 2, v_v_626_);
lean_ctor_set(v___x_618_, 1, v_k_625_);
lean_ctor_set(v___x_618_, 0, v___x_668_);
v___x_670_ = v___x_618_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_k_625_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_v_626_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_l_627_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_l_644_);
v___x_670_ = v_reuseFailAlloc_674_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; 
v___x_671_ = lean_nat_add(v___x_622_, v_size_623_);
if (lean_obj_tag(v_r_645_) == 0)
{
lean_object* v_size_672_; 
v_size_672_ = lean_ctor_get(v_r_645_, 0);
lean_inc(v_size_672_);
v___y_655_ = v___x_671_;
v___y_656_ = v___x_670_;
v___y_657_ = v_size_672_;
goto v___jp_654_;
}
else
{
lean_object* v___x_673_; 
v___x_673_ = lean_unsigned_to_nat(0u);
v___y_655_ = v___x_671_;
v___y_656_ = v___x_670_;
v___y_657_ = v___x_673_;
goto v___jp_654_;
}
}
}
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
lean_del_object(v___x_618_);
v___x_683_ = lean_nat_add(v___x_622_, v_size_624_);
lean_dec(v_size_624_);
v___x_684_ = lean_nat_add(v___x_683_, v_size_623_);
lean_dec(v___x_683_);
v___x_685_ = lean_nat_add(v___x_622_, v_size_623_);
v___x_686_ = lean_nat_add(v___x_685_, v_size_641_);
lean_dec(v___x_685_);
lean_inc_ref(v_r_616_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v_r_616_);
lean_ctor_set(v___x_638_, 3, v_r_628_);
lean_ctor_set(v___x_638_, 2, v_v_614_);
lean_ctor_set(v___x_638_, 1, v_k_613_);
lean_ctor_set(v___x_638_, 0, v___x_686_);
v___x_688_ = v___x_638_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_r_628_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_r_616_);
v___x_688_ = v_reuseFailAlloc_701_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_isSharedCheck_695_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_696_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_r_616_, 2);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_r_616_, 1);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_r_616_, 0);
lean_dec(v_unused_700_);
v___x_690_ = v_r_616_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_dec(v_r_616_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v___x_688_);
lean_ctor_set(v___x_690_, 3, v_l_627_);
lean_ctor_set(v___x_690_, 2, v_v_626_);
lean_ctor_set(v___x_690_, 1, v_k_625_);
lean_ctor_set(v___x_690_, 0, v___x_684_);
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_k_625_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_v_626_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_l_627_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v___x_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_708_; 
v_l_708_ = lean_ctor_get(v_impl_621_, 3);
if (lean_obj_tag(v_l_708_) == 0)
{
lean_object* v_r_709_; lean_object* v_k_710_; lean_object* v_v_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_722_; 
lean_inc_ref(v_l_708_);
v_r_709_ = lean_ctor_get(v_impl_621_, 4);
v_k_710_ = lean_ctor_get(v_impl_621_, 1);
v_v_711_ = lean_ctor_get(v_impl_621_, 2);
v_isSharedCheck_722_ = !lean_is_exclusive(v_impl_621_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_723_ = lean_ctor_get(v_impl_621_, 3);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_impl_621_, 0);
lean_dec(v_unused_724_);
v___x_713_ = v_impl_621_;
v_isShared_714_ = v_isSharedCheck_722_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_r_709_);
lean_inc(v_v_711_);
lean_inc(v_k_710_);
lean_dec(v_impl_621_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_722_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_709_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 3, v_r_709_);
lean_ctor_set(v___x_713_, 2, v_v_614_);
lean_ctor_set(v___x_713_, 1, v_k_613_);
lean_ctor_set(v___x_713_, 0, v___x_622_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_r_709_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_r_709_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v___x_717_);
lean_ctor_set(v___x_618_, 3, v_l_708_);
lean_ctor_set(v___x_618_, 2, v_v_711_);
lean_ctor_set(v___x_618_, 1, v_k_710_);
lean_ctor_set(v___x_618_, 0, v___x_715_);
v___x_719_ = v___x_618_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_710_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_711_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_l_708_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_r_725_; 
v_r_725_ = lean_ctor_get(v_impl_621_, 4);
lean_inc(v_r_725_);
if (lean_obj_tag(v_r_725_) == 0)
{
lean_object* v_k_726_; lean_object* v_v_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_750_; 
lean_inc(v_l_708_);
v_k_726_ = lean_ctor_get(v_impl_621_, 1);
v_v_727_ = lean_ctor_get(v_impl_621_, 2);
v_isSharedCheck_750_ = !lean_is_exclusive(v_impl_621_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; 
v_unused_751_ = lean_ctor_get(v_impl_621_, 4);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_impl_621_, 3);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_impl_621_, 0);
lean_dec(v_unused_753_);
v___x_729_ = v_impl_621_;
v_isShared_730_ = v_isSharedCheck_750_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_v_727_);
lean_inc(v_k_726_);
lean_dec(v_impl_621_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_750_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v_k_731_; lean_object* v_v_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_746_; 
v_k_731_ = lean_ctor_get(v_r_725_, 1);
v_v_732_ = lean_ctor_get(v_r_725_, 2);
v_isSharedCheck_746_ = !lean_is_exclusive(v_r_725_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; lean_object* v_unused_748_; lean_object* v_unused_749_; 
v_unused_747_ = lean_ctor_get(v_r_725_, 4);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v_r_725_, 3);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v_r_725_, 0);
lean_dec(v_unused_749_);
v___x_734_ = v_r_725_;
v_isShared_735_ = v_isSharedCheck_746_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_v_732_);
lean_inc(v_k_731_);
lean_dec(v_r_725_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_746_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = lean_unsigned_to_nat(3u);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 4, v_l_708_);
lean_ctor_set(v___x_734_, 3, v_l_708_);
lean_ctor_set(v___x_734_, 2, v_v_727_);
lean_ctor_set(v___x_734_, 1, v_k_726_);
lean_ctor_set(v___x_734_, 0, v___x_622_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_k_726_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_v_727_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_l_708_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_l_708_);
v___x_738_ = v_reuseFailAlloc_745_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 4, v_l_708_);
lean_ctor_set(v___x_729_, 2, v_v_614_);
lean_ctor_set(v___x_729_, 1, v_k_613_);
lean_ctor_set(v___x_729_, 0, v___x_622_);
v___x_740_ = v___x_729_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_l_708_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v_l_708_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v___x_740_);
lean_ctor_set(v___x_618_, 3, v___x_738_);
lean_ctor_set(v___x_618_, 2, v_v_732_);
lean_ctor_set(v___x_618_, 1, v_k_731_);
lean_ctor_set(v___x_618_, 0, v___x_736_);
v___x_742_ = v___x_618_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = lean_unsigned_to_nat(2u);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_r_725_);
lean_ctor_set(v___x_618_, 3, v_impl_621_);
lean_ctor_set(v___x_618_, 0, v___x_754_);
v___x_756_ = v___x_618_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v_impl_621_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v_r_725_);
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
case 1:
{
lean_object* v___x_759_; 
lean_dec(v_v_614_);
lean_dec(v_k_613_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 2, v_v_610_);
lean_ctor_set(v___x_618_, 1, v_k_609_);
v___x_759_ = v___x_618_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_size_612_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_k_609_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_v_610_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_l_615_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v_r_616_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
default: 
{
lean_object* v_impl_761_; lean_object* v___x_762_; 
lean_dec(v_size_612_);
v_impl_761_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_609_, v_v_610_, v_r_616_);
v___x_762_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_615_) == 0)
{
lean_object* v_size_763_; lean_object* v_size_764_; lean_object* v_k_765_; lean_object* v_v_766_; lean_object* v_l_767_; lean_object* v_r_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_size_763_ = lean_ctor_get(v_l_615_, 0);
v_size_764_ = lean_ctor_get(v_impl_761_, 0);
v_k_765_ = lean_ctor_get(v_impl_761_, 1);
v_v_766_ = lean_ctor_get(v_impl_761_, 2);
v_l_767_ = lean_ctor_get(v_impl_761_, 3);
lean_inc(v_l_767_);
v_r_768_ = lean_ctor_get(v_impl_761_, 4);
v___x_769_ = lean_unsigned_to_nat(3u);
v___x_770_ = lean_nat_mul(v___x_769_, v_size_763_);
v___x_771_ = lean_nat_dec_lt(v___x_770_, v_size_764_);
lean_dec(v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec(v_l_767_);
v___x_772_ = lean_nat_add(v___x_762_, v_size_763_);
v___x_773_ = lean_nat_add(v___x_772_, v_size_764_);
lean_dec(v___x_772_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_impl_761_);
lean_ctor_set(v___x_618_, 0, v___x_773_);
v___x_775_ = v___x_618_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_l_615_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_impl_761_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_840_; 
lean_inc(v_r_768_);
lean_inc(v_v_766_);
lean_inc(v_k_765_);
lean_inc(v_size_764_);
v_isSharedCheck_840_ = !lean_is_exclusive(v_impl_761_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; lean_object* v_unused_844_; lean_object* v_unused_845_; 
v_unused_841_ = lean_ctor_get(v_impl_761_, 4);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_impl_761_, 3);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_impl_761_, 2);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_impl_761_, 1);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_impl_761_, 0);
lean_dec(v_unused_845_);
v___x_778_ = v_impl_761_;
v_isShared_779_ = v_isSharedCheck_840_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_impl_761_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_840_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_size_780_; lean_object* v_k_781_; lean_object* v_v_782_; lean_object* v_l_783_; lean_object* v_r_784_; lean_object* v_size_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_size_780_ = lean_ctor_get(v_l_767_, 0);
v_k_781_ = lean_ctor_get(v_l_767_, 1);
v_v_782_ = lean_ctor_get(v_l_767_, 2);
v_l_783_ = lean_ctor_get(v_l_767_, 3);
v_r_784_ = lean_ctor_get(v_l_767_, 4);
v_size_785_ = lean_ctor_get(v_r_768_, 0);
v___x_786_ = lean_unsigned_to_nat(2u);
v___x_787_ = lean_nat_mul(v___x_786_, v_size_785_);
v___x_788_ = lean_nat_dec_lt(v_size_780_, v___x_787_);
lean_dec(v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_816_; 
lean_inc(v_r_784_);
lean_inc(v_l_783_);
lean_inc(v_v_782_);
lean_inc(v_k_781_);
v_isSharedCheck_816_ = !lean_is_exclusive(v_l_767_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; lean_object* v_unused_821_; 
v_unused_817_ = lean_ctor_get(v_l_767_, 4);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_l_767_, 3);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_l_767_, 2);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_l_767_, 1);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_l_767_, 0);
lean_dec(v_unused_821_);
v___x_790_ = v_l_767_;
v_isShared_791_ = v_isSharedCheck_816_;
goto v_resetjp_789_;
}
else
{
lean_dec(v_l_767_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_816_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_806_; 
v___x_792_ = lean_nat_add(v___x_762_, v_size_763_);
v___x_793_ = lean_nat_add(v___x_792_, v_size_764_);
lean_dec(v_size_764_);
if (lean_obj_tag(v_l_783_) == 0)
{
lean_object* v_size_814_; 
v_size_814_ = lean_ctor_get(v_l_783_, 0);
lean_inc(v_size_814_);
v___y_806_ = v_size_814_;
goto v___jp_805_;
}
else
{
lean_object* v___x_815_; 
v___x_815_ = lean_unsigned_to_nat(0u);
v___y_806_ = v___x_815_;
goto v___jp_805_;
}
v___jp_794_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_nat_add(v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec(v___y_796_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 4, v_r_768_);
lean_ctor_set(v___x_790_, 3, v_r_784_);
lean_ctor_set(v___x_790_, 2, v_v_766_);
lean_ctor_set(v___x_790_, 1, v_k_765_);
lean_ctor_set(v___x_790_, 0, v___x_798_);
v___x_800_ = v___x_790_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_k_765_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_v_766_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_r_784_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v_r_768_);
v___x_800_ = v_reuseFailAlloc_804_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v___x_800_);
lean_ctor_set(v___x_778_, 3, v___y_795_);
lean_ctor_set(v___x_778_, 2, v_v_782_);
lean_ctor_set(v___x_778_, 1, v_k_781_);
lean_ctor_set(v___x_778_, 0, v___x_793_);
v___x_802_ = v___x_778_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_k_781_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_v_782_);
lean_ctor_set(v_reuseFailAlloc_803_, 3, v___y_795_);
lean_ctor_set(v_reuseFailAlloc_803_, 4, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
v___jp_805_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_nat_add(v___x_792_, v___y_806_);
lean_dec(v___y_806_);
lean_dec(v___x_792_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_l_783_);
lean_ctor_set(v___x_618_, 0, v___x_807_);
v___x_809_ = v___x_618_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_l_615_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_l_783_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; 
v___x_810_ = lean_nat_add(v___x_762_, v_size_785_);
if (lean_obj_tag(v_r_784_) == 0)
{
lean_object* v_size_811_; 
v_size_811_ = lean_ctor_get(v_r_784_, 0);
lean_inc(v_size_811_);
v___y_795_ = v___x_809_;
v___y_796_ = v___x_810_;
v___y_797_ = v_size_811_;
goto v___jp_794_;
}
else
{
lean_object* v___x_812_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___y_795_ = v___x_809_;
v___y_796_ = v___x_810_;
v___y_797_ = v___x_812_;
goto v___jp_794_;
}
}
}
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
lean_del_object(v___x_618_);
v___x_822_ = lean_nat_add(v___x_762_, v_size_763_);
v___x_823_ = lean_nat_add(v___x_822_, v_size_764_);
lean_dec(v_size_764_);
v___x_824_ = lean_nat_add(v___x_822_, v_size_780_);
lean_dec(v___x_822_);
lean_inc_ref(v_l_615_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v_l_767_);
lean_ctor_set(v___x_778_, 3, v_l_615_);
lean_ctor_set(v___x_778_, 2, v_v_614_);
lean_ctor_set(v___x_778_, 1, v_k_613_);
lean_ctor_set(v___x_778_, 0, v___x_824_);
v___x_826_ = v___x_778_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v_l_615_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v_l_767_);
v___x_826_ = v_reuseFailAlloc_839_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_isSharedCheck_833_ = !lean_is_exclusive(v_l_615_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_834_ = lean_ctor_get(v_l_615_, 4);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_l_615_, 3);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_l_615_, 2);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_l_615_, 1);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_l_615_, 0);
lean_dec(v_unused_838_);
v___x_828_ = v_l_615_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_l_615_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 4, v_r_768_);
lean_ctor_set(v___x_828_, 3, v___x_826_);
lean_ctor_set(v___x_828_, 2, v_v_766_);
lean_ctor_set(v___x_828_, 1, v_k_765_);
lean_ctor_set(v___x_828_, 0, v___x_823_);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_765_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_v_766_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v_r_768_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_846_; 
v_l_846_ = lean_ctor_get(v_impl_761_, 3);
lean_inc(v_l_846_);
if (lean_obj_tag(v_l_846_) == 0)
{
lean_object* v_r_847_; lean_object* v_k_848_; lean_object* v_v_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_872_; 
v_r_847_ = lean_ctor_get(v_impl_761_, 4);
v_k_848_ = lean_ctor_get(v_impl_761_, 1);
v_v_849_ = lean_ctor_get(v_impl_761_, 2);
v_isSharedCheck_872_ = !lean_is_exclusive(v_impl_761_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; lean_object* v_unused_874_; 
v_unused_873_ = lean_ctor_get(v_impl_761_, 3);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_impl_761_, 0);
lean_dec(v_unused_874_);
v___x_851_ = v_impl_761_;
v_isShared_852_ = v_isSharedCheck_872_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_r_847_);
lean_inc(v_v_849_);
lean_inc(v_k_848_);
lean_dec(v_impl_761_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_872_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_k_853_; lean_object* v_v_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_868_; 
v_k_853_ = lean_ctor_get(v_l_846_, 1);
v_v_854_ = lean_ctor_get(v_l_846_, 2);
v_isSharedCheck_868_ = !lean_is_exclusive(v_l_846_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; lean_object* v_unused_870_; lean_object* v_unused_871_; 
v_unused_869_ = lean_ctor_get(v_l_846_, 4);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_l_846_, 3);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_l_846_, 0);
lean_dec(v_unused_871_);
v___x_856_ = v_l_846_;
v_isShared_857_ = v_isSharedCheck_868_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_v_854_);
lean_inc(v_k_853_);
lean_dec(v_l_846_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_868_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_847_, 2);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 4, v_r_847_);
lean_ctor_set(v___x_856_, 3, v_r_847_);
lean_ctor_set(v___x_856_, 2, v_v_614_);
lean_ctor_set(v___x_856_, 1, v_k_613_);
lean_ctor_set(v___x_856_, 0, v___x_762_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_r_847_);
lean_ctor_set(v_reuseFailAlloc_867_, 4, v_r_847_);
v___x_860_ = v_reuseFailAlloc_867_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
lean_inc(v_r_847_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 3, v_r_847_);
lean_ctor_set(v___x_851_, 0, v___x_762_);
v___x_862_ = v___x_851_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_r_847_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_r_847_);
v___x_862_ = v_reuseFailAlloc_866_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_864_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v___x_862_);
lean_ctor_set(v___x_618_, 3, v___x_860_);
lean_ctor_set(v___x_618_, 2, v_v_854_);
lean_ctor_set(v___x_618_, 1, v_k_853_);
lean_ctor_set(v___x_618_, 0, v___x_858_);
v___x_864_ = v___x_618_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_k_853_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_v_854_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
else
{
lean_object* v_r_875_; 
v_r_875_ = lean_ctor_get(v_impl_761_, 4);
lean_inc(v_r_875_);
if (lean_obj_tag(v_r_875_) == 0)
{
lean_object* v_k_876_; lean_object* v_v_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_888_; 
v_k_876_ = lean_ctor_get(v_impl_761_, 1);
v_v_877_ = lean_ctor_get(v_impl_761_, 2);
v_isSharedCheck_888_ = !lean_is_exclusive(v_impl_761_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; 
v_unused_889_ = lean_ctor_get(v_impl_761_, 4);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_impl_761_, 3);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_impl_761_, 0);
lean_dec(v_unused_891_);
v___x_879_ = v_impl_761_;
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_v_877_);
lean_inc(v_k_876_);
lean_dec(v_impl_761_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_unsigned_to_nat(3u);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 4, v_l_846_);
lean_ctor_set(v___x_879_, 2, v_v_614_);
lean_ctor_set(v___x_879_, 1, v_k_613_);
lean_ctor_set(v___x_879_, 0, v___x_762_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v_l_846_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v_l_846_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_r_875_);
lean_ctor_set(v___x_618_, 3, v___x_883_);
lean_ctor_set(v___x_618_, 2, v_v_877_);
lean_ctor_set(v___x_618_, 1, v_k_876_);
lean_ctor_set(v___x_618_, 0, v___x_881_);
v___x_885_ = v___x_618_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_k_876_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_v_877_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_r_875_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_unsigned_to_nat(2u);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 4, v_impl_761_);
lean_ctor_set(v___x_618_, 3, v_r_875_);
lean_ctor_set(v___x_618_, 0, v___x_892_);
v___x_894_ = v___x_618_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_r_875_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_impl_761_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
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
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_unsigned_to_nat(1u);
v___x_898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v_k_609_);
lean_ctor_set(v___x_898_, 2, v_v_610_);
lean_ctor_set(v___x_898_, 3, v_t_611_);
lean_ctor_set(v___x_898_, 4, v_t_611_);
return v___x_898_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object* v_k_899_, lean_object* v_t_900_){
_start:
{
if (lean_obj_tag(v_t_900_) == 0)
{
lean_object* v_k_901_; lean_object* v_l_902_; lean_object* v_r_903_; uint8_t v___x_904_; 
v_k_901_ = lean_ctor_get(v_t_900_, 1);
v_l_902_ = lean_ctor_get(v_t_900_, 3);
v_r_903_ = lean_ctor_get(v_t_900_, 4);
v___x_904_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_899_, v_k_901_);
switch(v___x_904_)
{
case 0:
{
v_t_900_ = v_l_902_;
goto _start;
}
case 1:
{
uint8_t v___x_906_; 
v___x_906_ = 1;
return v___x_906_;
}
default: 
{
v_t_900_ = v_r_903_;
goto _start;
}
}
}
else
{
uint8_t v___x_908_; 
v___x_908_ = 0;
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object* v_k_909_, lean_object* v_t_910_){
_start:
{
uint8_t v_res_911_; lean_object* v_r_912_; 
v_res_911_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_909_, v_t_910_);
lean_dec(v_t_910_);
lean_dec(v_k_909_);
v_r_912_ = lean_box(v_res_911_);
return v_r_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object* v___y_913_){
_start:
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = lean_box(1);
v___x_915_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v___y_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_box(0);
v___x_917_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___y_913_, v___x_916_, v___x_914_);
return v___x_917_;
}
else
{
lean_dec(v___y_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object* v_00_u03b2_920_, lean_object* v_k_921_, lean_object* v_t_922_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_921_, v_t_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object* v_00_u03b2_924_, lean_object* v_k_925_, lean_object* v_t_926_){
_start:
{
uint8_t v_res_927_; lean_object* v_r_928_; 
v_res_927_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(v_00_u03b2_924_, v_k_925_, v_t_926_);
lean_dec(v_t_926_);
lean_dec(v_k_925_);
v_r_928_ = lean_box(v_res_927_);
return v_r_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object* v_00_u03b2_929_, lean_object* v_k_930_, lean_object* v_v_931_, lean_object* v_t_932_, lean_object* v_hl_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_930_, v_v_931_, v_t_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_935_, lean_object* v_a_936_, lean_object* v_b_937_, lean_object* v_c_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_apply_2(v_f_935_, v_a_936_, v_c_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_940_, lean_object* v_____do__lift_941_){
_start:
{
lean_object* v_a_942_; lean_object* v___x_943_; 
v_a_942_ = lean_ctor_get(v_____do__lift_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref(v_____do__lift_941_);
v___x_943_ = lean_apply_2(v_toPure_940_, lean_box(0), v_a_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object* v_inst_944_, lean_object* v_m_945_, lean_object* v_init_946_, lean_object* v_f_947_){
_start:
{
lean_object* v_toApplicative_948_; lean_object* v_toBind_949_; lean_object* v_toPure_950_; lean_object* v___f_951_; lean_object* v___x_952_; lean_object* v___f_953_; lean_object* v___x_954_; 
v_toApplicative_948_ = lean_ctor_get(v_inst_944_, 0);
v_toBind_949_ = lean_ctor_get(v_inst_944_, 1);
lean_inc(v_toBind_949_);
v_toPure_950_ = lean_ctor_get(v_toApplicative_948_, 1);
lean_inc(v_toPure_950_);
v___f_951_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_951_, 0, v_f_947_);
v___x_952_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_944_, v___f_951_, v_init_946_, v_m_945_);
v___f_953_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_953_, 0, v_toPure_950_);
v___x_954_ = lean_apply_4(v_toBind_949_, lean_box(0), lean_box(0), v___x_952_, v___f_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object* v_m_955_, lean_object* v_inst_956_, lean_object* v_00_u03b2_957_, lean_object* v_m_958_, lean_object* v_init_959_, lean_object* v_f_960_){
_start:
{
lean_object* v_toApplicative_961_; lean_object* v_toBind_962_; lean_object* v_toPure_963_; lean_object* v___f_964_; lean_object* v___x_965_; lean_object* v___f_966_; lean_object* v___x_967_; 
v_toApplicative_961_ = lean_ctor_get(v_inst_956_, 0);
v_toBind_962_ = lean_ctor_get(v_inst_956_, 1);
lean_inc(v_toBind_962_);
v_toPure_963_ = lean_ctor_get(v_toApplicative_961_, 1);
lean_inc(v_toPure_963_);
v___f_964_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_964_, 0, v_f_960_);
v___x_965_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_956_, v___f_964_, v_init_959_, v_m_958_);
v___f_966_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_966_, 0, v_toPure_963_);
v___x_967_ = lean_apply_4(v_toBind_962_, lean_box(0), lean_box(0), v___x_965_, v___f_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_969_, 0, lean_box(0));
lean_closure_set(v___x_969_, 1, v_inst_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_970_, lean_object* v_inst_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_972_, 0, lean_box(0));
lean_closure_set(v___x_972_, 1, v_inst_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_973_, lean_object* v_fvarId_974_){
_start:
{
uint8_t v___x_975_; 
v___x_975_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_fvarId_974_, v_s_973_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_box(0);
v___x_977_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_974_, v___x_976_, v_s_973_);
return v___x_977_;
}
else
{
lean_dec(v_fvarId_974_);
return v_s_973_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_978_, lean_object* v_x_979_){
_start:
{
if (lean_obj_tag(v_x_979_) == 0)
{
lean_object* v_k_980_; lean_object* v_l_981_; lean_object* v_r_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_k_980_ = lean_ctor_get(v_x_979_, 1);
lean_inc(v_k_980_);
v_l_981_ = lean_ctor_get(v_x_979_, 3);
lean_inc(v_l_981_);
v_r_982_ = lean_ctor_get(v_x_979_, 4);
lean_inc(v_r_982_);
lean_dec_ref_known(v_x_979_, 5);
v___x_983_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_978_, v_l_981_);
v___x_984_ = l_Lean_FVarIdSet_insert(v___x_983_, v_k_980_);
v_init_978_ = v___x_984_;
v_x_979_ = v_r_982_;
goto _start;
}
else
{
return v_init_978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_986_, lean_object* v_vs_u2082_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_987_, v_vs_u2081_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_989_, lean_object* v_t_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_989_, v_t_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_992_){
_start:
{
lean_object* v___f_993_; lean_object* v___x_994_; 
v___f_993_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_994_ = l_Std_TreeSet_ofList___redArg(v_l_992_, v___f_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object* v_l_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_FVarIdSet_ofList(v_l_995_);
lean_dec(v_l_995_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_997_){
_start:
{
lean_object* v___f_998_; lean_object* v___x_999_; 
v___f_998_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_999_ = l_Std_TreeSet_ofArray___redArg(v_l_997_, v___f_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_FVarIdSet_ofArray(v_l_1000_);
lean_dec_ref(v_l_1000_);
return v_res_1001_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_unsigned_to_nat(16u);
v___x_1004_ = lean_mk_array(v___x_1003_, v___x_1002_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1012_, lean_object* v_fvarId_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1013_, v_a_1014_, v_s_1012_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1016_, lean_object* v_s_1017_, lean_object* v_fvarId_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1018_, v_a_1019_, v_s_1017_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_box(1);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg();
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_box(1);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_box(1);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg___boxed(lean_object* v___dummy_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_instEmptyCollectionFVarIdMap___redArg();
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_box(1);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_box(1);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg___boxed(lean_object* v___dummy_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_instInhabitedFVarIdMap___redArg();
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_box(1);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_box(0);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_box(0);
return v___x_1040_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_name_eq(v_x_1041_, v_x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
uint8_t v_res_1046_; lean_object* v_r_1047_; 
v_res_1046_ = l_Lean_instBEqMVarId_beq(v_x_1044_, v_x_1045_);
lean_dec(v_x_1045_);
lean_dec(v_x_1044_);
v_r_1047_ = lean_box(v_res_1046_);
return v_r_1047_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1050_){
_start:
{
uint64_t v___x_1051_; 
v___x_1051_ = 0ULL;
if (lean_obj_tag(v_x_1050_) == 0)
{
uint64_t v___x_1052_; 
v___x_1052_ = 8934034000889494153ULL;
return v___x_1052_;
}
else
{
uint64_t v_hash_1053_; uint64_t v___x_1054_; 
v_hash_1053_ = lean_ctor_get_uint64(v_x_1050_, sizeof(void*)*2);
v___x_1054_ = lean_uint64_mix_hash(v___x_1051_, v_hash_1053_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1055_){
_start:
{
uint64_t v_res_1056_; lean_object* v_r_1057_; 
v_res_1056_ = l_Lean_instHashableMVarId_hash(v_x_1055_);
lean_dec(v_x_1055_);
v_r_1057_ = lean_box_uint64(v_res_1056_);
return v_r_1057_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_box(1);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_box(1);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_box(1);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_box(1);
return v___x_1064_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1065_, lean_object* v_t_1066_){
_start:
{
if (lean_obj_tag(v_t_1066_) == 0)
{
lean_object* v_k_1067_; lean_object* v_l_1068_; lean_object* v_r_1069_; uint8_t v___x_1070_; 
v_k_1067_ = lean_ctor_get(v_t_1066_, 1);
v_l_1068_ = lean_ctor_get(v_t_1066_, 3);
v_r_1069_ = lean_ctor_get(v_t_1066_, 4);
v___x_1070_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1065_, v_k_1067_);
switch(v___x_1070_)
{
case 0:
{
v_t_1066_ = v_l_1068_;
goto _start;
}
case 1:
{
uint8_t v___x_1072_; 
v___x_1072_ = 1;
return v___x_1072_;
}
default: 
{
v_t_1066_ = v_r_1069_;
goto _start;
}
}
}
else
{
uint8_t v___x_1074_; 
v___x_1074_ = 0;
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1075_, lean_object* v_t_1076_){
_start:
{
uint8_t v_res_1077_; lean_object* v_r_1078_; 
v_res_1077_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1075_, v_t_1076_);
lean_dec(v_t_1076_);
lean_dec(v_k_1075_);
v_r_1078_ = lean_box(v_res_1077_);
return v_r_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1079_, lean_object* v_v_1080_, lean_object* v_t_1081_){
_start:
{
if (lean_obj_tag(v_t_1081_) == 0)
{
lean_object* v_size_1082_; lean_object* v_k_1083_; lean_object* v_v_1084_; lean_object* v_l_1085_; lean_object* v_r_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1366_; 
v_size_1082_ = lean_ctor_get(v_t_1081_, 0);
v_k_1083_ = lean_ctor_get(v_t_1081_, 1);
v_v_1084_ = lean_ctor_get(v_t_1081_, 2);
v_l_1085_ = lean_ctor_get(v_t_1081_, 3);
v_r_1086_ = lean_ctor_get(v_t_1081_, 4);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_t_1081_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1088_ = v_t_1081_;
v_isShared_1089_ = v_isSharedCheck_1366_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_r_1086_);
lean_inc(v_l_1085_);
lean_inc(v_v_1084_);
lean_inc(v_k_1083_);
lean_inc(v_size_1082_);
lean_dec(v_t_1081_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1366_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
uint8_t v___x_1090_; 
v___x_1090_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1079_, v_k_1083_);
switch(v___x_1090_)
{
case 0:
{
lean_object* v_impl_1091_; lean_object* v___x_1092_; 
lean_dec(v_size_1082_);
v_impl_1091_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1079_, v_v_1080_, v_l_1085_);
v___x_1092_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1086_) == 0)
{
lean_object* v_size_1093_; lean_object* v_size_1094_; lean_object* v_k_1095_; lean_object* v_v_1096_; lean_object* v_l_1097_; lean_object* v_r_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_size_1093_ = lean_ctor_get(v_r_1086_, 0);
v_size_1094_ = lean_ctor_get(v_impl_1091_, 0);
v_k_1095_ = lean_ctor_get(v_impl_1091_, 1);
v_v_1096_ = lean_ctor_get(v_impl_1091_, 2);
v_l_1097_ = lean_ctor_get(v_impl_1091_, 3);
v_r_1098_ = lean_ctor_get(v_impl_1091_, 4);
lean_inc(v_r_1098_);
v___x_1099_ = lean_unsigned_to_nat(3u);
v___x_1100_ = lean_nat_mul(v___x_1099_, v_size_1093_);
v___x_1101_ = lean_nat_dec_lt(v___x_1100_, v_size_1094_);
lean_dec(v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
lean_dec(v_r_1098_);
v___x_1102_ = lean_nat_add(v___x_1092_, v_size_1094_);
v___x_1103_ = lean_nat_add(v___x_1102_, v_size_1093_);
lean_dec(v___x_1102_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 3, v_impl_1091_);
lean_ctor_set(v___x_1088_, 0, v___x_1103_);
v___x_1105_ = v___x_1088_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_impl_1091_);
lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_r_1086_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
else
{
lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1172_; 
lean_inc(v_l_1097_);
lean_inc(v_v_1096_);
lean_inc(v_k_1095_);
lean_inc(v_size_1094_);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_impl_1091_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; 
v_unused_1173_ = lean_ctor_get(v_impl_1091_, 4);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_impl_1091_, 3);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_impl_1091_, 2);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_impl_1091_, 1);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_impl_1091_, 0);
lean_dec(v_unused_1177_);
v___x_1108_ = v_impl_1091_;
v_isShared_1109_ = v_isSharedCheck_1172_;
goto v_resetjp_1107_;
}
else
{
lean_dec(v_impl_1091_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1172_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_size_1110_; lean_object* v_size_1111_; lean_object* v_k_1112_; lean_object* v_v_1113_; lean_object* v_l_1114_; lean_object* v_r_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_size_1110_ = lean_ctor_get(v_l_1097_, 0);
v_size_1111_ = lean_ctor_get(v_r_1098_, 0);
v_k_1112_ = lean_ctor_get(v_r_1098_, 1);
v_v_1113_ = lean_ctor_get(v_r_1098_, 2);
v_l_1114_ = lean_ctor_get(v_r_1098_, 3);
v_r_1115_ = lean_ctor_get(v_r_1098_, 4);
v___x_1116_ = lean_unsigned_to_nat(2u);
v___x_1117_ = lean_nat_mul(v___x_1116_, v_size_1110_);
v___x_1118_ = lean_nat_dec_lt(v_size_1111_, v___x_1117_);
lean_dec(v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1147_; 
lean_inc(v_r_1115_);
lean_inc(v_l_1114_);
lean_inc(v_v_1113_);
lean_inc(v_k_1112_);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_r_1098_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1148_ = lean_ctor_get(v_r_1098_, 4);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_r_1098_, 3);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_r_1098_, 2);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_r_1098_, 1);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_r_1098_, 0);
lean_dec(v_unused_1152_);
v___x_1120_ = v_r_1098_;
v_isShared_1121_ = v_isSharedCheck_1147_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v_r_1098_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1147_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___x_1135_; lean_object* v___y_1137_; 
v___x_1122_ = lean_nat_add(v___x_1092_, v_size_1094_);
lean_dec(v_size_1094_);
v___x_1123_ = lean_nat_add(v___x_1122_, v_size_1093_);
lean_dec(v___x_1122_);
v___x_1135_ = lean_nat_add(v___x_1092_, v_size_1110_);
if (lean_obj_tag(v_l_1114_) == 0)
{
lean_object* v_size_1145_; 
v_size_1145_ = lean_ctor_get(v_l_1114_, 0);
lean_inc(v_size_1145_);
v___y_1137_ = v_size_1145_;
goto v___jp_1136_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v___y_1137_ = v___x_1146_;
goto v___jp_1136_;
}
v___jp_1124_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = lean_nat_add(v___y_1125_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec(v___y_1125_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_r_1086_);
lean_ctor_set(v___x_1120_, 3, v_r_1115_);
lean_ctor_set(v___x_1120_, 2, v_v_1084_);
lean_ctor_set(v___x_1120_, 1, v_k_1083_);
lean_ctor_set(v___x_1120_, 0, v___x_1128_);
v___x_1130_ = v___x_1120_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_r_1115_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v_r_1086_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v___x_1130_);
lean_ctor_set(v___x_1108_, 3, v___y_1126_);
lean_ctor_set(v___x_1108_, 2, v_v_1113_);
lean_ctor_set(v___x_1108_, 1, v_k_1112_);
lean_ctor_set(v___x_1108_, 0, v___x_1123_);
v___x_1132_ = v___x_1108_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_k_1112_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_v_1113_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v___y_1126_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
v___jp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_nat_add(v___x_1135_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec(v___x_1135_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 4, v_l_1114_);
lean_ctor_set(v___x_1088_, 3, v_l_1097_);
lean_ctor_set(v___x_1088_, 2, v_v_1096_);
lean_ctor_set(v___x_1088_, 1, v_k_1095_);
lean_ctor_set(v___x_1088_, 0, v___x_1138_);
v___x_1140_ = v___x_1088_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_l_1097_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_l_1114_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_nat_add(v___x_1092_, v_size_1093_);
if (lean_obj_tag(v_r_1115_) == 0)
{
lean_object* v_size_1142_; 
v_size_1142_ = lean_ctor_get(v_r_1115_, 0);
lean_inc(v_size_1142_);
v___y_1125_ = v___x_1141_;
v___y_1126_ = v___x_1140_;
v___y_1127_ = v_size_1142_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___y_1125_ = v___x_1141_;
v___y_1126_ = v___x_1140_;
v___y_1127_ = v___x_1143_;
goto v___jp_1124_;
}
}
}
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
lean_del_object(v___x_1088_);
v___x_1153_ = lean_nat_add(v___x_1092_, v_size_1094_);
lean_dec(v_size_1094_);
v___x_1154_ = lean_nat_add(v___x_1153_, v_size_1093_);
lean_dec(v___x_1153_);
v___x_1155_ = lean_nat_add(v___x_1092_, v_size_1093_);
v___x_1156_ = lean_nat_add(v___x_1155_, v_size_1111_);
lean_dec(v___x_1155_);
lean_inc_ref(v_r_1086_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v_r_1086_);
lean_ctor_set(v___x_1108_, 3, v_r_1098_);
lean_ctor_set(v___x_1108_, 2, v_v_1084_);
lean_ctor_set(v___x_1108_, 1, v_k_1083_);
lean_ctor_set(v___x_1108_, 0, v___x_1156_);
v___x_1158_ = v___x_1108_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v_r_1098_);
lean_ctor_set(v_reuseFailAlloc_1171_, 4, v_r_1086_);
v___x_1158_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_isSharedCheck_1165_ = !lean_is_exclusive(v_r_1086_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; 
v_unused_1166_ = lean_ctor_get(v_r_1086_, 4);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_r_1086_, 3);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_r_1086_, 2);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_r_1086_, 1);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_r_1086_, 0);
lean_dec(v_unused_1170_);
v___x_1160_ = v_r_1086_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_dec(v_r_1086_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 4, v___x_1158_);
lean_ctor_set(v___x_1160_, 3, v_l_1097_);
lean_ctor_set(v___x_1160_, 2, v_v_1096_);
lean_ctor_set(v___x_1160_, 1, v_k_1095_);
lean_ctor_set(v___x_1160_, 0, v___x_1154_);
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_l_1097_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v___x_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1178_; 
v_l_1178_ = lean_ctor_get(v_impl_1091_, 3);
if (lean_obj_tag(v_l_1178_) == 0)
{
lean_object* v_r_1179_; lean_object* v_k_1180_; lean_object* v_v_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1192_; 
lean_inc_ref(v_l_1178_);
v_r_1179_ = lean_ctor_get(v_impl_1091_, 4);
v_k_1180_ = lean_ctor_get(v_impl_1091_, 1);
v_v_1181_ = lean_ctor_get(v_impl_1091_, 2);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_impl_1091_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; lean_object* v_unused_1194_; 
v_unused_1193_ = lean_ctor_get(v_impl_1091_, 3);
lean_dec(v_unused_1193_);
v_unused_1194_ = lean_ctor_get(v_impl_1091_, 0);
lean_dec(v_unused_1194_);
v___x_1183_ = v_impl_1091_;
v_isShared_1184_ = v_isSharedCheck_1192_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_r_1179_);
lean_inc(v_v_1181_);
lean_inc(v_k_1180_);
lean_dec(v_impl_1091_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1192_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1179_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 3, v_r_1179_);
lean_ctor_set(v___x_1183_, 2, v_v_1084_);
lean_ctor_set(v___x_1183_, 1, v_k_1083_);
lean_ctor_set(v___x_1183_, 0, v___x_1092_);
v___x_1187_ = v___x_1183_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v_r_1179_);
lean_ctor_set(v_reuseFailAlloc_1191_, 4, v_r_1179_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 4, v___x_1187_);
lean_ctor_set(v___x_1088_, 3, v_l_1178_);
lean_ctor_set(v___x_1088_, 2, v_v_1181_);
lean_ctor_set(v___x_1088_, 1, v_k_1180_);
lean_ctor_set(v___x_1088_, 0, v___x_1185_);
v___x_1189_ = v___x_1088_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_k_1180_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_v_1181_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_l_1178_);
lean_ctor_set(v_reuseFailAlloc_1190_, 4, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v_r_1195_; 
v_r_1195_ = lean_ctor_get(v_impl_1091_, 4);
lean_inc(v_r_1195_);
if (lean_obj_tag(v_r_1195_) == 0)
{
lean_object* v_k_1196_; lean_object* v_v_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1220_; 
lean_inc(v_l_1178_);
v_k_1196_ = lean_ctor_get(v_impl_1091_, 1);
v_v_1197_ = lean_ctor_get(v_impl_1091_, 2);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_impl_1091_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; lean_object* v_unused_1222_; lean_object* v_unused_1223_; 
v_unused_1221_ = lean_ctor_get(v_impl_1091_, 4);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_impl_1091_, 3);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_impl_1091_, 0);
lean_dec(v_unused_1223_);
v___x_1199_ = v_impl_1091_;
v_isShared_1200_ = v_isSharedCheck_1220_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_v_1197_);
lean_inc(v_k_1196_);
lean_dec(v_impl_1091_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1220_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v_k_1201_; lean_object* v_v_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1216_; 
v_k_1201_ = lean_ctor_get(v_r_1195_, 1);
v_v_1202_ = lean_ctor_get(v_r_1195_, 2);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_r_1195_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; lean_object* v_unused_1218_; lean_object* v_unused_1219_; 
v_unused_1217_ = lean_ctor_get(v_r_1195_, 4);
lean_dec(v_unused_1217_);
v_unused_1218_ = lean_ctor_get(v_r_1195_, 3);
lean_dec(v_unused_1218_);
v_unused_1219_ = lean_ctor_get(v_r_1195_, 0);
lean_dec(v_unused_1219_);
v___x_1204_ = v_r_1195_;
v_isShared_1205_ = v_isSharedCheck_1216_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_v_1202_);
lean_inc(v_k_1201_);
lean_dec(v_r_1195_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1216_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = lean_unsigned_to_nat(3u);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 4, v_l_1178_);
lean_ctor_set(v___x_1204_, 3, v_l_1178_);
lean_ctor_set(v___x_1204_, 2, v_v_1197_);
lean_ctor_set(v___x_1204_, 1, v_k_1196_);
lean_ctor_set(v___x_1204_, 0, v___x_1092_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_k_1196_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_v_1197_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_l_1178_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_l_1178_);
v___x_1208_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 4, v_l_1178_);
lean_ctor_set(v___x_1199_, 2, v_v_1084_);
lean_ctor_set(v___x_1199_, 1, v_k_1083_);
lean_ctor_set(v___x_1199_, 0, v___x_1092_);
v___x_1210_ = v___x_1199_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_l_1178_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_l_1178_);
v___x_1210_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1212_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 4, v___x_1210_);
lean_ctor_set(v___x_1088_, 3, v___x_1208_);
lean_ctor_set(v___x_1088_, 2, v_v_1202_);
lean_ctor_set(v___x_1088_, 1, v_k_1201_);
lean_ctor_set(v___x_1088_, 0, v___x_1206_);
v___x_1212_ = v___x_1088_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_k_1201_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_v_1202_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = lean_unsigned_to_nat(2u);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 4, v_r_1195_);
lean_ctor_set(v___x_1088_, 3, v_impl_1091_);
lean_ctor_set(v___x_1088_, 0, v___x_1224_);
v___x_1226_ = v___x_1088_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_impl_1091_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_r_1195_);
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
case 1:
{
lean_object* v___x_1229_; 
lean_dec(v_v_1084_);
lean_dec(v_k_1083_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 2, v_v_1080_);
lean_ctor_set(v___x_1088_, 1, v_k_1079_);
v___x_1229_ = v___x_1088_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_size_1082_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_k_1079_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_v_1080_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_l_1085_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_r_1086_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
default: 
{
lean_object* v_impl_1231_; lean_object* v___x_1232_; 
lean_dec(v_size_1082_);
v_impl_1231_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1079_, v_v_1080_, v_r_1086_);
v___x_1232_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1085_) == 0)
{
lean_object* v_size_1233_; lean_object* v_size_1234_; lean_object* v_k_1235_; lean_object* v_v_1236_; lean_object* v_l_1237_; lean_object* v_r_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_size_1233_ = lean_ctor_get(v_l_1085_, 0);
v_size_1234_ = lean_ctor_get(v_impl_1231_, 0);
v_k_1235_ = lean_ctor_get(v_impl_1231_, 1);
v_v_1236_ = lean_ctor_get(v_impl_1231_, 2);
v_l_1237_ = lean_ctor_get(v_impl_1231_, 3);
lean_inc(v_l_1237_);
v_r_1238_ = lean_ctor_get(v_impl_1231_, 4);
v___x_1239_ = lean_unsigned_to_nat(3u);
v___x_1240_ = lean_nat_mul(v___x_1239_, v_size_1233_);
v___x_1241_ = lean_nat_dec_lt(v___x_1240_, v_size_1234_);
lean_dec(v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
lean_dec(v_l_1237_);
v___x_1242_ = lean_nat_add(v___x_1232_, v_size_1233_);
v___x_1243_ = lean_nat_add(v___x_1242_, v_size_1234_);
lean_dec(v___x_1242_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 4, v_impl_1231_);
lean_ctor_set(v___x_1088_, 0, v___x_1243_);
v___x_1245_ = v___x_1088_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_l_1085_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_impl_1231_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
else
{
lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1310_; 
lean_inc(v_r_1238_);
lean_inc(v_v_1236_);
lean_inc(v_k_1235_);
lean_inc(v_size_1234_);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_impl_1231_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; lean_object* v_unused_1312_; lean_object* v_unused_1313_; lean_object* v_unused_1314_; lean_object* v_unused_1315_; 
v_unused_1311_ = lean_ctor_get(v_impl_1231_, 4);
lean_dec(v_unused_1311_);
v_unused_1312_ = lean_ctor_get(v_impl_1231_, 3);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v_impl_1231_, 2);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v_impl_1231_, 1);
lean_dec(v_unused_1314_);
v_unused_1315_ = lean_ctor_get(v_impl_1231_, 0);
lean_dec(v_unused_1315_);
v___x_1248_ = v_impl_1231_;
v_isShared_1249_ = v_isSharedCheck_1310_;
goto v_resetjp_1247_;
}
else
{
lean_dec(v_impl_1231_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1310_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_size_1250_; lean_object* v_k_1251_; lean_object* v_v_1252_; lean_object* v_l_1253_; lean_object* v_r_1254_; lean_object* v_size_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_size_1250_ = lean_ctor_get(v_l_1237_, 0);
v_k_1251_ = lean_ctor_get(v_l_1237_, 1);
v_v_1252_ = lean_ctor_get(v_l_1237_, 2);
v_l_1253_ = lean_ctor_get(v_l_1237_, 3);
v_r_1254_ = lean_ctor_get(v_l_1237_, 4);
v_size_1255_ = lean_ctor_get(v_r_1238_, 0);
v___x_1256_ = lean_unsigned_to_nat(2u);
v___x_1257_ = lean_nat_mul(v___x_1256_, v_size_1255_);
v___x_1258_ = lean_nat_dec_lt(v_size_1250_, v___x_1257_);
lean_dec(v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1286_; 
lean_inc(v_r_1254_);
lean_inc(v_l_1253_);
lean_inc(v_v_1252_);
lean_inc(v_k_1251_);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_l_1237_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; lean_object* v_unused_1288_; lean_object* v_unused_1289_; lean_object* v_unused_1290_; lean_object* v_unused_1291_; 
v_unused_1287_ = lean_ctor_get(v_l_1237_, 4);
lean_dec(v_unused_1287_);
v_unused_1288_ = lean_ctor_get(v_l_1237_, 3);
lean_dec(v_unused_1288_);
v_unused_1289_ = lean_ctor_get(v_l_1237_, 2);
lean_dec(v_unused_1289_);
v_unused_1290_ = lean_ctor_get(v_l_1237_, 1);
lean_dec(v_unused_1290_);
v_unused_1291_ = lean_ctor_get(v_l_1237_, 0);
lean_dec(v_unused_1291_);
v___x_1260_ = v_l_1237_;
v_isShared_1261_ = v_isSharedCheck_1286_;
goto v_resetjp_1259_;
}
else
{
lean_dec(v_l_1237_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1286_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1276_; 
v___x_1262_ = lean_nat_add(v___x_1232_, v_size_1233_);
v___x_1263_ = lean_nat_add(v___x_1262_, v_size_1234_);
lean_dec(v_size_1234_);
if (lean_obj_tag(v_l_1253_) == 0)
{
lean_object* v_size_1284_; 
v_size_1284_ = lean_ctor_get(v_l_1253_, 0);
lean_inc(v_size_1284_);
v___y_1276_ = v_size_1284_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_unsigned_to_nat(0u);
v___y_1276_ = v___x_1285_;
goto v___jp_1275_;
}
v___jp_1264_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = lean_nat_add(v___y_1265_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec(v___y_1265_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 4, v_r_1238_);
lean_ctor_set(v___x_1260_, 3, v_r_1254_);
lean_ctor_set(v___x_1260_, 2, v_v_1236_);
lean_ctor_set(v___x_1260_, 1, v_k_1235_);
lean_ctor_set(v___x_1260_, 0, v___x_1268_);
v___x_1270_ = v___x_1260_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_k_1235_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_v_1236_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_r_1254_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_r_1238_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1272_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 4, v___x_1270_);
lean_ctor_set(v___x_1248_, 3, v___y_1266_);
lean_ctor_set(v___x_1248_, 2, v_v_1252_);
lean_ctor_set(v___x_1248_, 1, v_k_1251_);
lean_ctor_set(v___x_1248_, 0, v___x_1263_);
v___x_1272_ = v___x_1248_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_k_1251_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_v_1252_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v___y_1266_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
v___jp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_nat_add(v___x_1262_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec(v___x_1262_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 4, v_l_1253_);
lean_ctor_set(v___x_1088_, 0, v___x_1277_);
v___x_1279_ = v___x_1088_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_l_1085_);
lean_ctor_set(v_reuseFailAlloc_1283_, 4, v_l_1253_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_nat_add(v___x_1232_, v_size_1255_);
if (lean_obj_tag(v_r_1254_) == 0)
{
lean_object* v_size_1281_; 
v_size_1281_ = lean_ctor_get(v_r_1254_, 0);
lean_inc(v_size_1281_);
v___y_1265_ = v___x_1280_;
v___y_1266_ = v___x_1279_;
v___y_1267_ = v_size_1281_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_unsigned_to_nat(0u);
v___y_1265_ = v___x_1280_;
v___y_1266_ = v___x_1279_;
v___y_1267_ = v___x_1282_;
goto v___jp_1264_;
}
}
}
}
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
lean_del_object(v___x_1088_);
v___x_1292_ = lean_nat_add(v___x_1232_, v_size_1233_);
v___x_1293_ = lean_nat_add(v___x_1292_, v_size_1234_);
lean_dec(v_size_1234_);
v___x_1294_ = lean_nat_add(v___x_1292_, v_size_1250_);
lean_dec(v___x_1292_);
lean_inc_ref(v_l_1085_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 4, v_l_1237_);
lean_ctor_set(v___x_1248_, 3, v_l_1085_);
lean_ctor_set(v___x_1248_, 2, v_v_1084_);
lean_ctor_set(v___x_1248_, 1, v_k_1083_);
lean_ctor_set(v___x_1248_, 0, v___x_1294_);
v___x_1296_ = v___x_1248_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_l_1085_);
lean_ctor_set(v_reuseFailAlloc_1309_, 4, v_l_1237_);
v___x_1296_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_isSharedCheck_1303_ = !lean_is_exclusive(v_l_1085_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; lean_object* v_unused_1305_; lean_object* v_unused_1306_; lean_object* v_unused_1307_; lean_object* v_unused_1308_; 
v_unused_1304_ = lean_ctor_get(v_l_1085_, 4);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v_l_1085_, 3);
lean_dec(v_unused_1305_);
v_unused_1306_ = lean_ctor_get(v_l_1085_, 2);
lean_dec(v_unused_1306_);
v_unused_1307_ = lean_ctor_get(v_l_1085_, 1);
lean_dec(v_unused_1307_);
v_unused_1308_ = lean_ctor_get(v_l_1085_, 0);
lean_dec(v_unused_1308_);
v___x_1298_ = v_l_1085_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_dec(v_l_1085_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_r_1238_);
lean_ctor_set(v___x_1298_, 3, v___x_1296_);
lean_ctor_set(v___x_1298_, 2, v_v_1236_);
lean_ctor_set(v___x_1298_, 1, v_k_1235_);
lean_ctor_set(v___x_1298_, 0, v___x_1293_);
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_k_1235_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_v_1236_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_r_1238_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1316_; 
v_l_1316_ = lean_ctor_get(v_impl_1231_, 3);
lean_inc(v_l_1316_);
if (lean_obj_tag(v_l_1316_) == 0)
{
lean_object* v_r_1317_; lean_object* v_k_1318_; lean_object* v_v_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1342_; 
v_r_1317_ = lean_ctor_get(v_impl_1231_, 4);
v_k_1318_ = lean_ctor_get(v_impl_1231_, 1);
v_v_1319_ = lean_ctor_get(v_impl_1231_, 2);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_impl_1231_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; lean_object* v_unused_1344_; 
v_unused_1343_ = lean_ctor_get(v_impl_1231_, 3);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_impl_1231_, 0);
lean_dec(v_unused_1344_);
v___x_1321_ = v_impl_1231_;
v_isShared_1322_ = v_isSharedCheck_1342_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_r_1317_);
lean_inc(v_v_1319_);
lean_inc(v_k_1318_);
lean_dec(v_impl_1231_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1342_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_k_1323_; lean_object* v_v_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1338_; 
v_k_1323_ = lean_ctor_get(v_l_1316_, 1);
v_v_1324_ = lean_ctor_get(v_l_1316_, 2);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_l_1316_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; lean_object* v_unused_1340_; lean_object* v_unused_1341_; 
v_unused_1339_ = lean_ctor_get(v_l_1316_, 4);
lean_dec(v_unused_1339_);
v_unused_1340_ = lean_ctor_get(v_l_1316_, 3);
lean_dec(v_unused_1340_);
v_unused_1341_ = lean_ctor_get(v_l_1316_, 0);
lean_dec(v_unused_1341_);
v___x_1326_ = v_l_1316_;
v_isShared_1327_ = v_isSharedCheck_1338_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_v_1324_);
lean_inc(v_k_1323_);
lean_dec(v_l_1316_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1338_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1317_, 2);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 4, v_r_1317_);
lean_ctor_set(v___x_1326_, 3, v_r_1317_);
lean_ctor_set(v___x_1326_, 2, v_v_1084_);
lean_ctor_set(v___x_1326_, 1, v_k_1083_);
lean_ctor_set(v___x_1326_, 0, v___x_1232_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1337_, 3, v_r_1317_);
lean_ctor_set(v_reuseFailAlloc_1337_, 4, v_r_1317_);
v___x_1330_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1332_; 
lean_inc(v_r_1317_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 3, v_r_1317_);
lean_ctor_set(v___x_1321_, 0, v___x_1232_);
v___x_1332_ = v___x_1321_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v_r_1317_);
lean_ctor_set(v_reuseFailAlloc_1336_, 4, v_r_1317_);
v___x_1332_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1334_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 4, v___x_1332_);
lean_ctor_set(v___x_1088_, 3, v___x_1330_);
lean_ctor_set(v___x_1088_, 2, v_v_1324_);
lean_ctor_set(v___x_1088_, 1, v_k_1323_);
lean_ctor_set(v___x_1088_, 0, v___x_1328_);
v___x_1334_ = v___x_1088_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_k_1323_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_v_1324_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
}
else
{
lean_object* v_r_1345_; 
v_r_1345_ = lean_ctor_get(v_impl_1231_, 4);
lean_inc(v_r_1345_);
if (lean_obj_tag(v_r_1345_) == 0)
{
lean_object* v_k_1346_; lean_object* v_v_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1358_; 
v_k_1346_ = lean_ctor_get(v_impl_1231_, 1);
v_v_1347_ = lean_ctor_get(v_impl_1231_, 2);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_impl_1231_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; lean_object* v_unused_1360_; lean_object* v_unused_1361_; 
v_unused_1359_ = lean_ctor_get(v_impl_1231_, 4);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v_impl_1231_, 3);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_impl_1231_, 0);
lean_dec(v_unused_1361_);
v___x_1349_ = v_impl_1231_;
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_v_1347_);
lean_inc(v_k_1346_);
lean_dec(v_impl_1231_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_unsigned_to_nat(3u);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 4, v_l_1316_);
lean_ctor_set(v___x_1349_, 2, v_v_1084_);
lean_ctor_set(v___x_1349_, 1, v_k_1083_);
lean_ctor_set(v___x_1349_, 0, v___x_1232_);
v___x_1353_ = v___x_1349_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_l_1316_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_l_1316_);
v___x_1353_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1355_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 4, v_r_1345_);
lean_ctor_set(v___x_1088_, 3, v___x_1353_);
lean_ctor_set(v___x_1088_, 2, v_v_1347_);
lean_ctor_set(v___x_1088_, 1, v_k_1346_);
lean_ctor_set(v___x_1088_, 0, v___x_1351_);
v___x_1355_ = v___x_1088_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_k_1346_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_v_1347_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_r_1345_);
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
else
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = lean_unsigned_to_nat(2u);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 4, v_impl_1231_);
lean_ctor_set(v___x_1088_, 3, v_r_1345_);
lean_ctor_set(v___x_1088_, 0, v___x_1362_);
v___x_1364_ = v___x_1088_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_r_1345_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_impl_1231_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
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
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v_k_1079_);
lean_ctor_set(v___x_1368_, 2, v_v_1080_);
lean_ctor_set(v___x_1368_, 3, v_t_1081_);
lean_ctor_set(v___x_1368_, 4, v_t_1081_);
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1369_, lean_object* v_mvarId_1370_){
_start:
{
uint8_t v___x_1371_; 
v___x_1371_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1370_, v_s_1369_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_box(0);
v___x_1373_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1370_, v___x_1372_, v_s_1369_);
return v___x_1373_;
}
else
{
lean_dec(v_mvarId_1370_);
return v_s_1369_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1374_, lean_object* v_k_1375_, lean_object* v_t_1376_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1375_, v_t_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1378_, lean_object* v_k_1379_, lean_object* v_t_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1378_, v_k_1379_, v_t_1380_);
lean_dec(v_t_1380_);
lean_dec(v_k_1379_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1383_, lean_object* v_k_1384_, lean_object* v_v_1385_, lean_object* v_t_1386_, lean_object* v_hl_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1384_, v_v_1385_, v_t_1386_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1389_){
_start:
{
lean_object* v___f_1390_; lean_object* v___x_1391_; 
v___f_1390_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1391_ = l_Std_TreeSet_ofList___redArg(v_l_1389_, v___f_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_MVarIdSet_ofList(v_l_1392_);
lean_dec(v_l_1392_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1394_){
_start:
{
lean_object* v___f_1395_; lean_object* v___x_1396_; 
v___f_1395_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1396_ = l_Std_TreeSet_ofArray___redArg(v_l_1394_, v___f_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_MVarIdSet_ofArray(v_l_1397_);
lean_dec_ref(v_l_1397_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1399_, lean_object* v_m_1400_, lean_object* v_init_1401_, lean_object* v_f_1402_){
_start:
{
lean_object* v_toApplicative_1403_; lean_object* v_toBind_1404_; lean_object* v_toPure_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___f_1408_; lean_object* v___x_1409_; 
v_toApplicative_1403_ = lean_ctor_get(v_inst_1399_, 0);
v_toBind_1404_ = lean_ctor_get(v_inst_1399_, 1);
lean_inc(v_toBind_1404_);
v_toPure_1405_ = lean_ctor_get(v_toApplicative_1403_, 1);
lean_inc(v_toPure_1405_);
v___f_1406_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1406_, 0, v_f_1402_);
v___x_1407_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1399_, v___f_1406_, v_init_1401_, v_m_1400_);
v___f_1408_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1408_, 0, v_toPure_1405_);
v___x_1409_ = lean_apply_4(v_toBind_1404_, lean_box(0), lean_box(0), v___x_1407_, v___f_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1410_, lean_object* v_inst_1411_, lean_object* v_00_u03b2_1412_, lean_object* v_m_1413_, lean_object* v_init_1414_, lean_object* v_f_1415_){
_start:
{
lean_object* v_toApplicative_1416_; lean_object* v_toBind_1417_; lean_object* v_toPure_1418_; lean_object* v___f_1419_; lean_object* v___x_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; 
v_toApplicative_1416_ = lean_ctor_get(v_inst_1411_, 0);
v_toBind_1417_ = lean_ctor_get(v_inst_1411_, 1);
lean_inc(v_toBind_1417_);
v_toPure_1418_ = lean_ctor_get(v_toApplicative_1416_, 1);
lean_inc(v_toPure_1418_);
v___f_1419_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1419_, 0, v_f_1415_);
v___x_1420_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1411_, v___f_1419_, v_init_1414_, v_m_1413_);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1421_, 0, v_toPure_1418_);
v___x_1422_ = lean_apply_4(v_toBind_1417_, lean_box(0), lean_box(0), v___x_1420_, v___f_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1424_, 0, lean_box(0));
lean_closure_set(v___x_1424_, 1, v_inst_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1425_, lean_object* v_inst_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1427_, 0, lean_box(0));
lean_closure_set(v___x_1427_, 1, v_inst_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1428_, lean_object* v_mvarId_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1429_, v_a_1430_, v_s_1428_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1432_, lean_object* v_s_1433_, lean_object* v_mvarId_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1434_, v_a_1435_, v_s_1433_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_box(1);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg();
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_box(1);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_box(1);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg___boxed(lean_object* v___dummy_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_instEmptyCollectionMVarIdMap___redArg();
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_box(1);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1449_, lean_object* v_a_1450_, lean_object* v_b_1451_, lean_object* v_c_1452_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v_a_1450_);
lean_ctor_set(v___x_1453_, 1, v_b_1451_);
v___x_1454_ = lean_apply_2(v_f_1449_, v___x_1453_, v_c_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1455_, lean_object* v_m_1456_, lean_object* v_init_1457_, lean_object* v_f_1458_){
_start:
{
lean_object* v_toApplicative_1459_; lean_object* v_toBind_1460_; lean_object* v_toPure_1461_; lean_object* v___f_1462_; lean_object* v___x_1463_; lean_object* v___f_1464_; lean_object* v___x_1465_; 
v_toApplicative_1459_ = lean_ctor_get(v_inst_1455_, 0);
v_toBind_1460_ = lean_ctor_get(v_inst_1455_, 1);
lean_inc(v_toBind_1460_);
v_toPure_1461_ = lean_ctor_get(v_toApplicative_1459_, 1);
lean_inc(v_toPure_1461_);
v___f_1462_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1462_, 0, v_f_1458_);
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1455_, v___f_1462_, v_init_1457_, v_m_1456_);
v___f_1464_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1464_, 0, v_toPure_1461_);
v___x_1465_ = lean_apply_4(v_toBind_1460_, lean_box(0), lean_box(0), v___x_1463_, v___f_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1466_, lean_object* v_00_u03b1_1467_, lean_object* v_inst_1468_, lean_object* v_00_u03b2_1469_, lean_object* v_m_1470_, lean_object* v_init_1471_, lean_object* v_f_1472_){
_start:
{
lean_object* v_toApplicative_1473_; lean_object* v_toBind_1474_; lean_object* v_toPure_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; 
v_toApplicative_1473_ = lean_ctor_get(v_inst_1468_, 0);
v_toBind_1474_ = lean_ctor_get(v_inst_1468_, 1);
lean_inc(v_toBind_1474_);
v_toPure_1475_ = lean_ctor_get(v_toApplicative_1473_, 1);
lean_inc(v_toPure_1475_);
v___f_1476_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1476_, 0, v_f_1472_);
v___x_1477_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1468_, v___f_1476_, v_init_1471_, v_m_1470_);
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1478_, 0, v_toPure_1475_);
v___x_1479_ = lean_apply_4(v_toBind_1474_, lean_box(0), lean_box(0), v___x_1477_, v___f_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1481_, 0, lean_box(0));
lean_closure_set(v___x_1481_, 1, lean_box(0));
lean_closure_set(v___x_1481_, 2, v_inst_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1482_, lean_object* v_00_u03b1_1483_, lean_object* v_inst_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1485_, 0, lean_box(0));
lean_closure_set(v___x_1485_, 1, lean_box(0));
lean_closure_set(v___x_1485_, 2, v_inst_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_box(1);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg___boxed(lean_object* v___dummy_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_instInhabitedMVarIdMap___redArg();
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_box(1);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl(lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_obj_tag_nat(v_x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl___boxed(lean_object* v_x_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Expr_ctorIdx___impl(v_x_1494_);
lean_dec_ref(v_x_1494_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1496_, lean_object* v_k_1497_){
_start:
{
switch(lean_obj_tag(v_t_1496_))
{
case 4:
{
lean_object* v_declName_1498_; lean_object* v_us_1499_; lean_object* v___x_1500_; 
v_declName_1498_ = lean_ctor_get(v_t_1496_, 0);
lean_inc(v_declName_1498_);
v_us_1499_ = lean_ctor_get(v_t_1496_, 1);
lean_inc(v_us_1499_);
lean_dec_ref_known(v_t_1496_, 2);
v___x_1500_ = lean_apply_2(v_k_1497_, v_declName_1498_, v_us_1499_);
return v___x_1500_;
}
case 5:
{
lean_object* v_fn_1501_; lean_object* v_arg_1502_; lean_object* v___x_1503_; 
v_fn_1501_ = lean_ctor_get(v_t_1496_, 0);
lean_inc_ref(v_fn_1501_);
v_arg_1502_ = lean_ctor_get(v_t_1496_, 1);
lean_inc_ref(v_arg_1502_);
lean_dec_ref_known(v_t_1496_, 2);
v___x_1503_ = lean_apply_2(v_k_1497_, v_fn_1501_, v_arg_1502_);
return v___x_1503_;
}
case 6:
{
lean_object* v_binderName_1504_; lean_object* v_binderType_1505_; lean_object* v_body_1506_; uint8_t v_binderInfo_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_binderName_1504_ = lean_ctor_get(v_t_1496_, 0);
lean_inc(v_binderName_1504_);
v_binderType_1505_ = lean_ctor_get(v_t_1496_, 1);
lean_inc_ref(v_binderType_1505_);
v_body_1506_ = lean_ctor_get(v_t_1496_, 2);
lean_inc_ref(v_body_1506_);
v_binderInfo_1507_ = lean_ctor_get_uint8(v_t_1496_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1496_, 3);
v___x_1508_ = lean_box(v_binderInfo_1507_);
v___x_1509_ = lean_apply_4(v_k_1497_, v_binderName_1504_, v_binderType_1505_, v_body_1506_, v___x_1508_);
return v___x_1509_;
}
case 7:
{
lean_object* v_binderName_1510_; lean_object* v_binderType_1511_; lean_object* v_body_1512_; uint8_t v_binderInfo_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v_binderName_1510_ = lean_ctor_get(v_t_1496_, 0);
lean_inc(v_binderName_1510_);
v_binderType_1511_ = lean_ctor_get(v_t_1496_, 1);
lean_inc_ref(v_binderType_1511_);
v_body_1512_ = lean_ctor_get(v_t_1496_, 2);
lean_inc_ref(v_body_1512_);
v_binderInfo_1513_ = lean_ctor_get_uint8(v_t_1496_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1496_, 3);
v___x_1514_ = lean_box(v_binderInfo_1513_);
v___x_1515_ = lean_apply_4(v_k_1497_, v_binderName_1510_, v_binderType_1511_, v_body_1512_, v___x_1514_);
return v___x_1515_;
}
case 8:
{
lean_object* v_declName_1516_; lean_object* v_type_1517_; lean_object* v_value_1518_; lean_object* v_body_1519_; uint8_t v_nondep_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_declName_1516_ = lean_ctor_get(v_t_1496_, 0);
lean_inc(v_declName_1516_);
v_type_1517_ = lean_ctor_get(v_t_1496_, 1);
lean_inc_ref(v_type_1517_);
v_value_1518_ = lean_ctor_get(v_t_1496_, 2);
lean_inc_ref(v_value_1518_);
v_body_1519_ = lean_ctor_get(v_t_1496_, 3);
lean_inc_ref(v_body_1519_);
v_nondep_1520_ = lean_ctor_get_uint8(v_t_1496_, sizeof(void*)*4);
lean_dec_ref_known(v_t_1496_, 4);
v___x_1521_ = lean_box(v_nondep_1520_);
v___x_1522_ = lean_apply_5(v_k_1497_, v_declName_1516_, v_type_1517_, v_value_1518_, v_body_1519_, v___x_1521_);
return v___x_1522_;
}
case 9:
{
lean_object* v_a_1523_; lean_object* v___x_1524_; 
v_a_1523_ = lean_ctor_get(v_t_1496_, 0);
lean_inc_ref(v_a_1523_);
lean_dec_ref_known(v_t_1496_, 1);
v___x_1524_ = lean_apply_1(v_k_1497_, v_a_1523_);
return v___x_1524_;
}
case 10:
{
lean_object* v_data_1525_; lean_object* v_expr_1526_; lean_object* v___x_1527_; 
v_data_1525_ = lean_ctor_get(v_t_1496_, 0);
lean_inc(v_data_1525_);
v_expr_1526_ = lean_ctor_get(v_t_1496_, 1);
lean_inc_ref(v_expr_1526_);
lean_dec_ref_known(v_t_1496_, 2);
v___x_1527_ = lean_apply_2(v_k_1497_, v_data_1525_, v_expr_1526_);
return v___x_1527_;
}
case 11:
{
lean_object* v_typeName_1528_; lean_object* v_idx_1529_; lean_object* v_struct_1530_; lean_object* v___x_1531_; 
v_typeName_1528_ = lean_ctor_get(v_t_1496_, 0);
lean_inc(v_typeName_1528_);
v_idx_1529_ = lean_ctor_get(v_t_1496_, 1);
lean_inc(v_idx_1529_);
v_struct_1530_ = lean_ctor_get(v_t_1496_, 2);
lean_inc_ref(v_struct_1530_);
lean_dec_ref_known(v_t_1496_, 3);
v___x_1531_ = lean_apply_3(v_k_1497_, v_typeName_1528_, v_idx_1529_, v_struct_1530_);
return v___x_1531_;
}
default: 
{
lean_object* v_deBruijnIndex_1532_; lean_object* v___x_1533_; 
v_deBruijnIndex_1532_ = lean_ctor_get(v_t_1496_, 0);
lean_inc(v_deBruijnIndex_1532_);
lean_dec_ref(v_t_1496_);
v___x_1533_ = lean_apply_1(v_k_1497_, v_deBruijnIndex_1532_);
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1534_, lean_object* v_ctorIdx_1535_, lean_object* v_t_1536_, lean_object* v_h_1537_, lean_object* v_k_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_Expr_ctorElim___redArg(v_t_1536_, v_k_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1540_, lean_object* v_ctorIdx_1541_, lean_object* v_t_1542_, lean_object* v_h_1543_, lean_object* v_k_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Expr_ctorElim(v_motive_1540_, v_ctorIdx_1541_, v_t_1542_, v_h_1543_, v_k_1544_);
lean_dec(v_ctorIdx_1541_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1546_, lean_object* v_bvar_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Expr_ctorElim___redArg(v_t_1546_, v_bvar_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1549_, lean_object* v_t_1550_, lean_object* v_h_1551_, lean_object* v_bvar_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Expr_ctorElim___redArg(v_t_1550_, v_bvar_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1554_, lean_object* v_fvar_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Expr_ctorElim___redArg(v_t_1554_, v_fvar_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1557_, lean_object* v_t_1558_, lean_object* v_h_1559_, lean_object* v_fvar_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Expr_ctorElim___redArg(v_t_1558_, v_fvar_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1562_, lean_object* v_mvar_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Expr_ctorElim___redArg(v_t_1562_, v_mvar_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1565_, lean_object* v_t_1566_, lean_object* v_h_1567_, lean_object* v_mvar_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Expr_ctorElim___redArg(v_t_1566_, v_mvar_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1570_, lean_object* v_sort_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Expr_ctorElim___redArg(v_t_1570_, v_sort_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1573_, lean_object* v_t_1574_, lean_object* v_h_1575_, lean_object* v_sort_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Expr_ctorElim___redArg(v_t_1574_, v_sort_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1578_, lean_object* v_const_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_Expr_ctorElim___redArg(v_t_1578_, v_const_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1581_, lean_object* v_t_1582_, lean_object* v_h_1583_, lean_object* v_const_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Expr_ctorElim___redArg(v_t_1582_, v_const_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1586_, lean_object* v_app_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_Expr_ctorElim___redArg(v_t_1586_, v_app_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1589_, lean_object* v_t_1590_, lean_object* v_h_1591_, lean_object* v_app_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Expr_ctorElim___redArg(v_t_1590_, v_app_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1594_, lean_object* v_lam_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Expr_ctorElim___redArg(v_t_1594_, v_lam_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1597_, lean_object* v_t_1598_, lean_object* v_h_1599_, lean_object* v_lam_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Expr_ctorElim___redArg(v_t_1598_, v_lam_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1602_, lean_object* v_forallE_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Expr_ctorElim___redArg(v_t_1602_, v_forallE_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1605_, lean_object* v_t_1606_, lean_object* v_h_1607_, lean_object* v_forallE_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Expr_ctorElim___redArg(v_t_1606_, v_forallE_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1610_, lean_object* v_letE_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Expr_ctorElim___redArg(v_t_1610_, v_letE_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1613_, lean_object* v_t_1614_, lean_object* v_h_1615_, lean_object* v_letE_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Expr_ctorElim___redArg(v_t_1614_, v_letE_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1618_, lean_object* v_lit_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Expr_ctorElim___redArg(v_t_1618_, v_lit_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1621_, lean_object* v_t_1622_, lean_object* v_h_1623_, lean_object* v_lit_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Expr_ctorElim___redArg(v_t_1622_, v_lit_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1626_, lean_object* v_mdata_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Expr_ctorElim___redArg(v_t_1626_, v_mdata_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1629_, lean_object* v_t_1630_, lean_object* v_h_1631_, lean_object* v_mdata_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Expr_ctorElim___redArg(v_t_1630_, v_mdata_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1634_, lean_object* v_proj_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Expr_ctorElim___redArg(v_t_1634_, v_proj_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1637_, lean_object* v_t_1638_, lean_object* v_h_1639_, lean_object* v_proj_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Expr_ctorElim___redArg(v_t_1638_, v_proj_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1643_){
_start:
{
uint64_t v_res_1644_; lean_object* v_r_1645_; 
v_res_1644_ = lean_expr_data(v_a_00___x40___internal___hyg_1643_);
lean_dec_ref(v_a_00___x40___internal___hyg_1643_);
v_r_1645_ = lean_box_uint64(v_res_1644_);
return v_r_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1646_, lean_object* v_bvar_1647_, lean_object* v_fvar_1648_, lean_object* v_mvar_1649_, lean_object* v_sort_1650_, lean_object* v_const_1651_, lean_object* v_app_1652_, lean_object* v_lam_1653_, lean_object* v_forallE_1654_, lean_object* v_letE_1655_, lean_object* v_lit_1656_, lean_object* v_mdata_1657_, lean_object* v_proj_1658_){
_start:
{
switch(lean_obj_tag(v_t_1646_))
{
case 0:
{
lean_object* v_deBruijnIndex_1659_; lean_object* v___x_1660_; 
lean_dec(v_proj_1658_);
lean_dec(v_mdata_1657_);
lean_dec(v_lit_1656_);
lean_dec(v_letE_1655_);
lean_dec(v_forallE_1654_);
lean_dec(v_lam_1653_);
lean_dec(v_app_1652_);
lean_dec(v_const_1651_);
lean_dec(v_sort_1650_);
lean_dec(v_mvar_1649_);
lean_dec(v_fvar_1648_);
v_deBruijnIndex_1659_ = lean_ctor_get(v_t_1646_, 0);
lean_inc(v_deBruijnIndex_1659_);
lean_dec_ref_known(v_t_1646_, 1);
v___x_1660_ = lean_apply_1(v_bvar_1647_, v_deBruijnIndex_1659_);
return v___x_1660_;
}
case 1:
{
lean_object* v_fvarId_1661_; lean_object* v___x_1662_; 
lean_dec(v_proj_1658_);
lean_dec(v_mdata_1657_);
lean_dec(v_lit_1656_);
lean_dec(v_letE_1655_);
lean_dec(v_forallE_1654_);
lean_dec(v_lam_1653_);
lean_dec(v_app_1652_);
lean_dec(v_const_1651_);
lean_dec(v_sort_1650_);
lean_dec(v_mvar_1649_);
lean_dec(v_bvar_1647_);
v_fvarId_1661_ = lean_ctor_get(v_t_1646_, 0);
lean_inc(v_fvarId_1661_);
lean_dec_ref_known(v_t_1646_, 1);
v___x_1662_ = lean_apply_1(v_fvar_1648_, v_fvarId_1661_);
return v___x_1662_;
}
case 2:
{
lean_object* v_mvarId_1663_; lean_object* v___x_1664_; 
lean_dec(v_proj_1658_);
lean_dec(v_mdata_1657_);
lean_dec(v_lit_1656_);
lean_dec(v_letE_1655_);
lean_dec(v_forallE_1654_);
lean_dec(v_lam_1653_);
lean_dec(v_app_1652_);
lean_dec(v_const_1651_);
lean_dec(v_sort_1650_);
lean_dec(v_fvar_1648_);
lean_dec(v_bvar_1647_);
v_mvarId_1663_ = lean_ctor_get(v_t_1646_, 0);
lean_inc(v_mvarId_1663_);
lean_dec_ref_known(v_t_1646_, 1);
v___x_1664_ = lean_apply_1(v_mvar_1649_, v_mvarId_1663_);
return v___x_1664_;
}
case 3:
{
lean_object* v_u_1665_; lean_object* v___x_1666_; 
lean_dec(v_proj_1658_);
lean_dec(v_mdata_1657_);
lean_dec(v_lit_1656_);
lean_dec(v_letE_1655_);
lean_dec(v_forallE_1654_);
lean_dec(v_lam_1653_);
lean_dec(v_app_1652_);
lean_dec(v_const_1651_);
lean_dec(v_mvar_1649_);
lean_dec(v_fvar_1648_);
lean_dec(v_bvar_1647_);
v_u_1665_ = lean_ctor_get(v_t_1646_, 0);
lean_inc(v_u_1665_);
lean_dec_ref_known(v_t_1646_, 1);
v___x_1666_ = lean_apply_1(v_sort_1650_, v_u_1665_);
return v___x_1666_;
}
case 4:
{
lean_object* v_declName_1667_; lean_object* v_us_1668_; lean_object* v___x_1669_; 
lean_dec(v_proj_1658_);
lean_dec(v_mdata_1657_);
lean_dec(v_lit_1656_);
lean_dec(v_letE_1655_);
lean_dec(v_forallE_1654_);
lean_dec(v_lam_1653_);
lean_dec(v_app_1652_);
lean_dec(v_sort_1650_);
lean_dec(v_mvar_1649_);
lean_dec(v_fvar_1648_);
lean_dec(v_bvar_1647_);
v_declName_1667_ = lean_ctor_get(v_t_1646_, 0);
lean_inc(v_declName_1667_);
v_us_1668_ = lean_ctor_get(v_t_1646_, 1);
lean_inc(v_us_1668_);
lean_dec_ref_known(v_t_1646_, 2);
v___x_1669_ = lean_apply_2(v_const_1651_, v_declName_1667_, v_us_1668_);
return v___x_1669_;
}
case 5:
{
lean_object* v_fn_1670_; lean_object* v_arg_1671_; lean_object* v___x_1672_; 
lean_dec(v_proj_1658_);
lean_dec(v_mdata_1657_);
lean_dec(v_lit_1656_);
lean_dec(v_letE_1655_);
lean_dec(v_forallE_1654_);
lean_dec(v_lam_1653_);
lean_dec(v_const_1651_);
lean_dec(v_sort_1650_);
lean_dec(v_mvar_1649_);
lean_dec(v_fvar_1648_);
lean_dec(v_bvar_1647_);
v_fn_1670_ = lean_ctor_get(v_t_1646_, 0);
lean_inc_ref(v_fn_1670_);
v_arg_1671_ = lean_ctor_get(v_t_1646_, 1);
lean_inc_ref(v_arg_1671_);
lean_dec_ref_known(v_t_1646_, 2);
v___x_1672_ = lean_apply_2(v_app_1652_, v_fn_1670_, v_arg_1671_);
return v___x_1672_;
}
case 6:
{
lean_object* v_binderName_1673_; lean_object* v_binderType_1674_; lean_object* v_body_1675_; uint8_t v_binderInfo_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v_proj_1658_);
lean_dec(v_mdata_1657_);
lean_dec(v_lit_1656_);
lean_dec(v_letE_1655_);
lean_dec(v_forallE_1654_);
lean_dec(v_app_1652_);
lean_dec(v_const_1651_);
lean_dec(v_sort_1650_);
lean_dec(v_mvar_1649_);
lean_dec(v_fvar_1648_);
lean_dec(v_bvar_1647_);
v_binderName_1673_ = lean_ctor_get(v_t_1646_, 0);
lean_inc(v_binderName_1673_);
v_binderType_1674_ = lean_ctor_get(v_t_1646_, 1);
lean_inc_ref(v_binderType_1674_);
v_body_1675_ = lean_ctor_get(v_t_1646_, 2);
lean_inc_ref(v_body_1675_);
v_binderInfo_1676_ = lean_ctor_get_uint8(v_t_1646_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1646_, 3);
v___x_1677_ = lean_box(v_binderInfo_1676_);
v___x_1678_ = lean_apply_4(v_lam_1653_, v_binderName_1673_, v_binderType_1674_, v_body_1675_, v___x_1677_);
return v___x_1678_;
}
case 7:
{
lean_object* v_binderName_1679_; lean_object* v_binderType_1680_; lean_object* v_body_1681_; uint8_t v_binderInfo_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec(v_proj_1658_);
lean_dec(v_mdata_1657_);
lean_dec(v_lit_1656_);
lean_dec(v_letE_1655_);
lean_dec(v_lam_1653_);
lean_dec(v_app_1652_);
lean_dec(v_const_1651_);
lean_dec(v_sort_1650_);
lean_dec(v_mvar_1649_);
lean_dec(v_fvar_1648_);
lean_dec(v_bvar_1647_);
v_binderName_1679_ = lean_ctor_get(v_t_1646_, 0);
lean_inc(v_binderName_1679_);
v_binderType_1680_ = lean_ctor_get(v_t_1646_, 1);
lean_inc_ref(v_binderType_1680_);
v_body_1681_ = lean_ctor_get(v_t_1646_, 2);
lean_inc_ref(v_body_1681_);
v_binderInfo_1682_ = lean_ctor_get_uint8(v_t_1646_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1646_, 3);
v___x_1683_ = lean_box(v_binderInfo_1682_);
v___x_1684_ = lean_apply_4(v_forallE_1654_, v_binderName_1679_, v_binderType_1680_, v_body_1681_, v___x_1683_);
return v___x_1684_;
}
case 8:
{
lean_object* v_declName_1685_; lean_object* v_type_1686_; lean_object* v_value_1687_; lean_object* v_body_1688_; uint8_t v_nondep_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_proj_1658_);
lean_dec(v_mdata_1657_);
lean_dec(v_lit_1656_);
lean_dec(v_forallE_1654_);
lean_dec(v_lam_1653_);
lean_dec(v_app_1652_);
lean_dec(v_const_1651_);
lean_dec(v_sort_1650_);
lean_dec(v_mvar_1649_);
lean_dec(v_fvar_1648_);
lean_dec(v_bvar_1647_);
v_declName_1685_ = lean_ctor_get(v_t_1646_, 0);
lean_inc(v_declName_1685_);
v_type_1686_ = lean_ctor_get(v_t_1646_, 1);
lean_inc_ref(v_type_1686_);
v_value_1687_ = lean_ctor_get(v_t_1646_, 2);
lean_inc_ref(v_value_1687_);
v_body_1688_ = lean_ctor_get(v_t_1646_, 3);
lean_inc_ref(v_body_1688_);
v_nondep_1689_ = lean_ctor_get_uint8(v_t_1646_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1646_, 4);
v___x_1690_ = lean_box(v_nondep_1689_);
v___x_1691_ = lean_apply_5(v_letE_1655_, v_declName_1685_, v_type_1686_, v_value_1687_, v_body_1688_, v___x_1690_);
return v___x_1691_;
}
case 9:
{
lean_object* v_a_1692_; lean_object* v___x_1693_; 
lean_dec(v_proj_1658_);
lean_dec(v_mdata_1657_);
lean_dec(v_letE_1655_);
lean_dec(v_forallE_1654_);
lean_dec(v_lam_1653_);
lean_dec(v_app_1652_);
lean_dec(v_const_1651_);
lean_dec(v_sort_1650_);
lean_dec(v_mvar_1649_);
lean_dec(v_fvar_1648_);
lean_dec(v_bvar_1647_);
v_a_1692_ = lean_ctor_get(v_t_1646_, 0);
lean_inc_ref(v_a_1692_);
lean_dec_ref_known(v_t_1646_, 1);
v___x_1693_ = lean_apply_1(v_lit_1656_, v_a_1692_);
return v___x_1693_;
}
case 10:
{
lean_object* v_data_1694_; lean_object* v_expr_1695_; lean_object* v___x_1696_; 
lean_dec(v_proj_1658_);
lean_dec(v_lit_1656_);
lean_dec(v_letE_1655_);
lean_dec(v_forallE_1654_);
lean_dec(v_lam_1653_);
lean_dec(v_app_1652_);
lean_dec(v_const_1651_);
lean_dec(v_sort_1650_);
lean_dec(v_mvar_1649_);
lean_dec(v_fvar_1648_);
lean_dec(v_bvar_1647_);
v_data_1694_ = lean_ctor_get(v_t_1646_, 0);
lean_inc(v_data_1694_);
v_expr_1695_ = lean_ctor_get(v_t_1646_, 1);
lean_inc_ref(v_expr_1695_);
lean_dec_ref_known(v_t_1646_, 2);
v___x_1696_ = lean_apply_2(v_mdata_1657_, v_data_1694_, v_expr_1695_);
return v___x_1696_;
}
default: 
{
lean_object* v_typeName_1697_; lean_object* v_idx_1698_; lean_object* v_struct_1699_; lean_object* v___x_1700_; 
lean_dec(v_mdata_1657_);
lean_dec(v_lit_1656_);
lean_dec(v_letE_1655_);
lean_dec(v_forallE_1654_);
lean_dec(v_lam_1653_);
lean_dec(v_app_1652_);
lean_dec(v_const_1651_);
lean_dec(v_sort_1650_);
lean_dec(v_mvar_1649_);
lean_dec(v_fvar_1648_);
lean_dec(v_bvar_1647_);
v_typeName_1697_ = lean_ctor_get(v_t_1646_, 0);
lean_inc(v_typeName_1697_);
v_idx_1698_ = lean_ctor_get(v_t_1646_, 1);
lean_inc(v_idx_1698_);
v_struct_1699_ = lean_ctor_get(v_t_1646_, 2);
lean_inc_ref(v_struct_1699_);
lean_dec_ref_known(v_t_1646_, 3);
v___x_1700_ = lean_apply_3(v_proj_1658_, v_typeName_1697_, v_idx_1698_, v_struct_1699_);
return v___x_1700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1701_, lean_object* v_t_1702_, lean_object* v_bvar_1703_, lean_object* v_fvar_1704_, lean_object* v_mvar_1705_, lean_object* v_sort_1706_, lean_object* v_const_1707_, lean_object* v_app_1708_, lean_object* v_lam_1709_, lean_object* v_forallE_1710_, lean_object* v_letE_1711_, lean_object* v_lit_1712_, lean_object* v_mdata_1713_, lean_object* v_proj_1714_){
_start:
{
switch(lean_obj_tag(v_t_1702_))
{
case 0:
{
lean_object* v_deBruijnIndex_1715_; lean_object* v___x_1716_; 
lean_dec(v_proj_1714_);
lean_dec(v_mdata_1713_);
lean_dec(v_lit_1712_);
lean_dec(v_letE_1711_);
lean_dec(v_forallE_1710_);
lean_dec(v_lam_1709_);
lean_dec(v_app_1708_);
lean_dec(v_const_1707_);
lean_dec(v_sort_1706_);
lean_dec(v_mvar_1705_);
lean_dec(v_fvar_1704_);
v_deBruijnIndex_1715_ = lean_ctor_get(v_t_1702_, 0);
lean_inc(v_deBruijnIndex_1715_);
lean_dec_ref_known(v_t_1702_, 1);
v___x_1716_ = lean_apply_1(v_bvar_1703_, v_deBruijnIndex_1715_);
return v___x_1716_;
}
case 1:
{
lean_object* v_fvarId_1717_; lean_object* v___x_1718_; 
lean_dec(v_proj_1714_);
lean_dec(v_mdata_1713_);
lean_dec(v_lit_1712_);
lean_dec(v_letE_1711_);
lean_dec(v_forallE_1710_);
lean_dec(v_lam_1709_);
lean_dec(v_app_1708_);
lean_dec(v_const_1707_);
lean_dec(v_sort_1706_);
lean_dec(v_mvar_1705_);
lean_dec(v_bvar_1703_);
v_fvarId_1717_ = lean_ctor_get(v_t_1702_, 0);
lean_inc(v_fvarId_1717_);
lean_dec_ref_known(v_t_1702_, 1);
v___x_1718_ = lean_apply_1(v_fvar_1704_, v_fvarId_1717_);
return v___x_1718_;
}
case 2:
{
lean_object* v_mvarId_1719_; lean_object* v___x_1720_; 
lean_dec(v_proj_1714_);
lean_dec(v_mdata_1713_);
lean_dec(v_lit_1712_);
lean_dec(v_letE_1711_);
lean_dec(v_forallE_1710_);
lean_dec(v_lam_1709_);
lean_dec(v_app_1708_);
lean_dec(v_const_1707_);
lean_dec(v_sort_1706_);
lean_dec(v_fvar_1704_);
lean_dec(v_bvar_1703_);
v_mvarId_1719_ = lean_ctor_get(v_t_1702_, 0);
lean_inc(v_mvarId_1719_);
lean_dec_ref_known(v_t_1702_, 1);
v___x_1720_ = lean_apply_1(v_mvar_1705_, v_mvarId_1719_);
return v___x_1720_;
}
case 3:
{
lean_object* v_u_1721_; lean_object* v___x_1722_; 
lean_dec(v_proj_1714_);
lean_dec(v_mdata_1713_);
lean_dec(v_lit_1712_);
lean_dec(v_letE_1711_);
lean_dec(v_forallE_1710_);
lean_dec(v_lam_1709_);
lean_dec(v_app_1708_);
lean_dec(v_const_1707_);
lean_dec(v_mvar_1705_);
lean_dec(v_fvar_1704_);
lean_dec(v_bvar_1703_);
v_u_1721_ = lean_ctor_get(v_t_1702_, 0);
lean_inc(v_u_1721_);
lean_dec_ref_known(v_t_1702_, 1);
v___x_1722_ = lean_apply_1(v_sort_1706_, v_u_1721_);
return v___x_1722_;
}
case 4:
{
lean_object* v_declName_1723_; lean_object* v_us_1724_; lean_object* v___x_1725_; 
lean_dec(v_proj_1714_);
lean_dec(v_mdata_1713_);
lean_dec(v_lit_1712_);
lean_dec(v_letE_1711_);
lean_dec(v_forallE_1710_);
lean_dec(v_lam_1709_);
lean_dec(v_app_1708_);
lean_dec(v_sort_1706_);
lean_dec(v_mvar_1705_);
lean_dec(v_fvar_1704_);
lean_dec(v_bvar_1703_);
v_declName_1723_ = lean_ctor_get(v_t_1702_, 0);
lean_inc(v_declName_1723_);
v_us_1724_ = lean_ctor_get(v_t_1702_, 1);
lean_inc(v_us_1724_);
lean_dec_ref_known(v_t_1702_, 2);
v___x_1725_ = lean_apply_2(v_const_1707_, v_declName_1723_, v_us_1724_);
return v___x_1725_;
}
case 5:
{
lean_object* v_fn_1726_; lean_object* v_arg_1727_; lean_object* v___x_1728_; 
lean_dec(v_proj_1714_);
lean_dec(v_mdata_1713_);
lean_dec(v_lit_1712_);
lean_dec(v_letE_1711_);
lean_dec(v_forallE_1710_);
lean_dec(v_lam_1709_);
lean_dec(v_const_1707_);
lean_dec(v_sort_1706_);
lean_dec(v_mvar_1705_);
lean_dec(v_fvar_1704_);
lean_dec(v_bvar_1703_);
v_fn_1726_ = lean_ctor_get(v_t_1702_, 0);
lean_inc_ref(v_fn_1726_);
v_arg_1727_ = lean_ctor_get(v_t_1702_, 1);
lean_inc_ref(v_arg_1727_);
lean_dec_ref_known(v_t_1702_, 2);
v___x_1728_ = lean_apply_2(v_app_1708_, v_fn_1726_, v_arg_1727_);
return v___x_1728_;
}
case 6:
{
lean_object* v_binderName_1729_; lean_object* v_binderType_1730_; lean_object* v_body_1731_; uint8_t v_binderInfo_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec(v_proj_1714_);
lean_dec(v_mdata_1713_);
lean_dec(v_lit_1712_);
lean_dec(v_letE_1711_);
lean_dec(v_forallE_1710_);
lean_dec(v_app_1708_);
lean_dec(v_const_1707_);
lean_dec(v_sort_1706_);
lean_dec(v_mvar_1705_);
lean_dec(v_fvar_1704_);
lean_dec(v_bvar_1703_);
v_binderName_1729_ = lean_ctor_get(v_t_1702_, 0);
lean_inc(v_binderName_1729_);
v_binderType_1730_ = lean_ctor_get(v_t_1702_, 1);
lean_inc_ref(v_binderType_1730_);
v_body_1731_ = lean_ctor_get(v_t_1702_, 2);
lean_inc_ref(v_body_1731_);
v_binderInfo_1732_ = lean_ctor_get_uint8(v_t_1702_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1702_, 3);
v___x_1733_ = lean_box(v_binderInfo_1732_);
v___x_1734_ = lean_apply_4(v_lam_1709_, v_binderName_1729_, v_binderType_1730_, v_body_1731_, v___x_1733_);
return v___x_1734_;
}
case 7:
{
lean_object* v_binderName_1735_; lean_object* v_binderType_1736_; lean_object* v_body_1737_; uint8_t v_binderInfo_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v_proj_1714_);
lean_dec(v_mdata_1713_);
lean_dec(v_lit_1712_);
lean_dec(v_letE_1711_);
lean_dec(v_lam_1709_);
lean_dec(v_app_1708_);
lean_dec(v_const_1707_);
lean_dec(v_sort_1706_);
lean_dec(v_mvar_1705_);
lean_dec(v_fvar_1704_);
lean_dec(v_bvar_1703_);
v_binderName_1735_ = lean_ctor_get(v_t_1702_, 0);
lean_inc(v_binderName_1735_);
v_binderType_1736_ = lean_ctor_get(v_t_1702_, 1);
lean_inc_ref(v_binderType_1736_);
v_body_1737_ = lean_ctor_get(v_t_1702_, 2);
lean_inc_ref(v_body_1737_);
v_binderInfo_1738_ = lean_ctor_get_uint8(v_t_1702_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1702_, 3);
v___x_1739_ = lean_box(v_binderInfo_1738_);
v___x_1740_ = lean_apply_4(v_forallE_1710_, v_binderName_1735_, v_binderType_1736_, v_body_1737_, v___x_1739_);
return v___x_1740_;
}
case 8:
{
lean_object* v_declName_1741_; lean_object* v_type_1742_; lean_object* v_value_1743_; lean_object* v_body_1744_; uint8_t v_nondep_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec(v_proj_1714_);
lean_dec(v_mdata_1713_);
lean_dec(v_lit_1712_);
lean_dec(v_forallE_1710_);
lean_dec(v_lam_1709_);
lean_dec(v_app_1708_);
lean_dec(v_const_1707_);
lean_dec(v_sort_1706_);
lean_dec(v_mvar_1705_);
lean_dec(v_fvar_1704_);
lean_dec(v_bvar_1703_);
v_declName_1741_ = lean_ctor_get(v_t_1702_, 0);
lean_inc(v_declName_1741_);
v_type_1742_ = lean_ctor_get(v_t_1702_, 1);
lean_inc_ref(v_type_1742_);
v_value_1743_ = lean_ctor_get(v_t_1702_, 2);
lean_inc_ref(v_value_1743_);
v_body_1744_ = lean_ctor_get(v_t_1702_, 3);
lean_inc_ref(v_body_1744_);
v_nondep_1745_ = lean_ctor_get_uint8(v_t_1702_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1702_, 4);
v___x_1746_ = lean_box(v_nondep_1745_);
v___x_1747_ = lean_apply_5(v_letE_1711_, v_declName_1741_, v_type_1742_, v_value_1743_, v_body_1744_, v___x_1746_);
return v___x_1747_;
}
case 9:
{
lean_object* v_a_1748_; lean_object* v___x_1749_; 
lean_dec(v_proj_1714_);
lean_dec(v_mdata_1713_);
lean_dec(v_letE_1711_);
lean_dec(v_forallE_1710_);
lean_dec(v_lam_1709_);
lean_dec(v_app_1708_);
lean_dec(v_const_1707_);
lean_dec(v_sort_1706_);
lean_dec(v_mvar_1705_);
lean_dec(v_fvar_1704_);
lean_dec(v_bvar_1703_);
v_a_1748_ = lean_ctor_get(v_t_1702_, 0);
lean_inc_ref(v_a_1748_);
lean_dec_ref_known(v_t_1702_, 1);
v___x_1749_ = lean_apply_1(v_lit_1712_, v_a_1748_);
return v___x_1749_;
}
case 10:
{
lean_object* v_data_1750_; lean_object* v_expr_1751_; lean_object* v___x_1752_; 
lean_dec(v_proj_1714_);
lean_dec(v_lit_1712_);
lean_dec(v_letE_1711_);
lean_dec(v_forallE_1710_);
lean_dec(v_lam_1709_);
lean_dec(v_app_1708_);
lean_dec(v_const_1707_);
lean_dec(v_sort_1706_);
lean_dec(v_mvar_1705_);
lean_dec(v_fvar_1704_);
lean_dec(v_bvar_1703_);
v_data_1750_ = lean_ctor_get(v_t_1702_, 0);
lean_inc(v_data_1750_);
v_expr_1751_ = lean_ctor_get(v_t_1702_, 1);
lean_inc_ref(v_expr_1751_);
lean_dec_ref_known(v_t_1702_, 2);
v___x_1752_ = lean_apply_2(v_mdata_1713_, v_data_1750_, v_expr_1751_);
return v___x_1752_;
}
default: 
{
lean_object* v_typeName_1753_; lean_object* v_idx_1754_; lean_object* v_struct_1755_; lean_object* v___x_1756_; 
lean_dec(v_mdata_1713_);
lean_dec(v_lit_1712_);
lean_dec(v_letE_1711_);
lean_dec(v_forallE_1710_);
lean_dec(v_lam_1709_);
lean_dec(v_app_1708_);
lean_dec(v_const_1707_);
lean_dec(v_sort_1706_);
lean_dec(v_mvar_1705_);
lean_dec(v_fvar_1704_);
lean_dec(v_bvar_1703_);
v_typeName_1753_ = lean_ctor_get(v_t_1702_, 0);
lean_inc(v_typeName_1753_);
v_idx_1754_ = lean_ctor_get(v_t_1702_, 1);
lean_inc(v_idx_1754_);
v_struct_1755_ = lean_ctor_get(v_t_1702_, 2);
lean_inc_ref(v_struct_1755_);
lean_dec_ref_known(v_t_1702_, 3);
v___x_1756_ = lean_apply_3(v_proj_1714_, v_typeName_1753_, v_idx_1754_, v_struct_1755_);
return v___x_1756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1757_){
_start:
{
uint64_t v___x_1758_; uint64_t v___x_1759_; uint64_t v___x_1760_; uint32_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint32_t v___x_1764_; uint8_t v___x_1765_; uint64_t v___x_1766_; lean_object* v___x_1767_; 
v___x_1758_ = 7ULL;
v___x_1759_ = lean_uint64_of_nat(v_deBruijnIndex_1757_);
v___x_1760_ = lean_uint64_mix_hash(v___x_1758_, v___x_1759_);
v___x_1761_ = lean_uint64_to_uint32(v___x_1760_);
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_nat_add(v_deBruijnIndex_1757_, v___x_1762_);
v___x_1764_ = 0;
v___x_1765_ = 0;
v___x_1766_ = lean_expr_mk_data(v___x_1761_, v___x_1763_, v___x_1764_, v___x_1765_, v___x_1765_, v___x_1765_, v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1767_, 0, v_deBruijnIndex_1757_);
lean_ctor_set_uint64(v___x_1767_, sizeof(void*)*1, v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1768_){
_start:
{
uint64_t v___x_1769_; uint64_t v___x_1770_; uint64_t v___x_1771_; uint32_t v___x_1772_; lean_object* v___x_1773_; uint32_t v___x_1774_; uint8_t v___x_1775_; uint8_t v___x_1776_; uint64_t v___x_1777_; lean_object* v___x_1778_; 
v___x_1769_ = 13ULL;
v___x_1770_ = l_Lean_instHashableFVarId_hash(v_fvarId_1768_);
v___x_1771_ = lean_uint64_mix_hash(v___x_1769_, v___x_1770_);
v___x_1772_ = lean_uint64_to_uint32(v___x_1771_);
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = 0;
v___x_1775_ = 1;
v___x_1776_ = 0;
v___x_1777_ = lean_expr_mk_data(v___x_1772_, v___x_1773_, v___x_1774_, v___x_1775_, v___x_1776_, v___x_1776_, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1778_, 0, v_fvarId_1768_);
lean_ctor_set_uint64(v___x_1778_, sizeof(void*)*1, v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1779_){
_start:
{
uint64_t v___x_1780_; uint64_t v___x_1781_; uint64_t v___x_1782_; uint32_t v___x_1783_; lean_object* v___x_1784_; uint32_t v___x_1785_; uint8_t v___x_1786_; uint8_t v___x_1787_; uint64_t v___x_1788_; lean_object* v___x_1789_; 
v___x_1780_ = 17ULL;
v___x_1781_ = l_Lean_instHashableMVarId_hash(v_mvarId_1779_);
v___x_1782_ = lean_uint64_mix_hash(v___x_1780_, v___x_1781_);
v___x_1783_ = lean_uint64_to_uint32(v___x_1782_);
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = 0;
v___x_1786_ = 0;
v___x_1787_ = 1;
v___x_1788_ = lean_expr_mk_data(v___x_1783_, v___x_1784_, v___x_1785_, v___x_1786_, v___x_1787_, v___x_1786_, v___x_1786_);
v___x_1789_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1789_, 0, v_mvarId_1779_);
lean_ctor_set_uint64(v___x_1789_, sizeof(void*)*1, v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1790_){
_start:
{
uint64_t v___x_1791_; uint64_t v___x_1792_; uint64_t v___x_1793_; uint32_t v___x_1794_; lean_object* v___x_1795_; uint32_t v___x_1796_; uint8_t v___x_1797_; uint8_t v___x_1798_; uint8_t v___x_1799_; uint64_t v___x_1800_; lean_object* v___x_1801_; 
v___x_1791_ = 11ULL;
v___x_1792_ = l_Lean_Level_hash(v_u_1790_);
v___x_1793_ = lean_uint64_mix_hash(v___x_1791_, v___x_1792_);
v___x_1794_ = lean_uint64_to_uint32(v___x_1793_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = 0;
v___x_1797_ = 0;
v___x_1798_ = l_Lean_Level_hasMVar(v_u_1790_);
v___x_1799_ = l_Lean_Level_hasParam(v_u_1790_);
v___x_1800_ = lean_expr_mk_data(v___x_1794_, v___x_1795_, v___x_1796_, v___x_1797_, v___x_1797_, v___x_1798_, v___x_1799_);
v___x_1801_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1801_, 0, v_u_1790_);
lean_ctor_set_uint64(v___x_1801_, sizeof(void*)*1, v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1802_, lean_object* v_arg_1803_){
_start:
{
uint64_t v___x_1804_; uint64_t v___x_1805_; uint64_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1804_ = lean_expr_data(v_fn_1802_);
v___x_1805_ = lean_expr_data(v_arg_1803_);
v___x_1806_ = lean_expr_mk_app_data(v___x_1804_, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1807_, 0, v_fn_1802_);
lean_ctor_set(v___x_1807_, 1, v_arg_1803_);
lean_ctor_set_uint64(v___x_1807_, sizeof(void*)*2, v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1808_, lean_object* v_binderType_1809_, lean_object* v_body_1810_, uint8_t v_binderInfo_1811_){
_start:
{
uint32_t v___x_1812_; uint64_t v___x_1813_; uint32_t v___x_1814_; uint32_t v___x_1815_; uint64_t v___x_1816_; uint32_t v___x_1817_; uint32_t v___x_1818_; lean_object* v___y_1820_; uint8_t v___y_1821_; uint8_t v___y_1822_; uint8_t v___y_1823_; uint32_t v___y_1824_; uint8_t v___y_1825_; lean_object* v___y_1829_; uint8_t v___y_1830_; uint8_t v___y_1831_; uint32_t v___y_1832_; uint8_t v___y_1833_; lean_object* v___y_1837_; uint8_t v___y_1838_; uint32_t v___y_1839_; uint8_t v___y_1840_; lean_object* v___y_1844_; uint32_t v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1850_; uint32_t v___y_1851_; lean_object* v___y_1857_; uint32_t v___x_1863_; lean_object* v___x_1864_; uint32_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1812_ = 29;
v___x_1813_ = lean_expr_data(v_binderType_1809_);
v___x_1814_ = lean_uint64_to_uint32(v___x_1813_);
v___x_1815_ = lean_uint32_mix_hash(v___x_1812_, v___x_1814_);
v___x_1816_ = lean_expr_data(v_body_1810_);
v___x_1817_ = lean_uint64_to_uint32(v___x_1816_);
v___x_1818_ = lean_uint32_mix_hash(v___x_1815_, v___x_1817_);
v___x_1863_ = l_Lean_Expr_Data_looseBVarRange(v___x_1813_);
v___x_1864_ = lean_uint32_to_nat(v___x_1863_);
v___x_1865_ = l_Lean_Expr_Data_looseBVarRange(v___x_1816_);
v___x_1866_ = lean_uint32_to_nat(v___x_1865_);
v___x_1867_ = lean_unsigned_to_nat(1u);
v___x_1868_ = lean_nat_sub(v___x_1866_, v___x_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_nat_dec_le(v___x_1864_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_dec(v___x_1868_);
v___y_1857_ = v___x_1864_;
goto v___jp_1856_;
}
else
{
lean_dec(v___x_1864_);
v___y_1857_ = v___x_1868_;
goto v___jp_1856_;
}
v___jp_1819_:
{
uint64_t v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_expr_mk_data(v___x_1818_, v___y_1820_, v___y_1824_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1825_);
v___x_1827_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1827_, 0, v_binderName_1808_);
lean_ctor_set(v___x_1827_, 1, v_binderType_1809_);
lean_ctor_set(v___x_1827_, 2, v_body_1810_);
lean_ctor_set_uint64(v___x_1827_, sizeof(void*)*3, v___x_1826_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*3 + 8, v_binderInfo_1811_);
return v___x_1827_;
}
v___jp_1828_:
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Lean_Expr_Data_hasLevelParam(v___x_1813_);
if (v___x_1834_ == 0)
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Expr_Data_hasLevelParam(v___x_1816_);
v___y_1820_ = v___y_1829_;
v___y_1821_ = v___y_1830_;
v___y_1822_ = v___y_1831_;
v___y_1823_ = v___y_1833_;
v___y_1824_ = v___y_1832_;
v___y_1825_ = v___x_1835_;
goto v___jp_1819_;
}
else
{
v___y_1820_ = v___y_1829_;
v___y_1821_ = v___y_1830_;
v___y_1822_ = v___y_1831_;
v___y_1823_ = v___y_1833_;
v___y_1824_ = v___y_1832_;
v___y_1825_ = v___x_1834_;
goto v___jp_1819_;
}
}
v___jp_1836_:
{
uint8_t v___x_1841_; 
v___x_1841_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1813_);
if (v___x_1841_ == 0)
{
uint8_t v___x_1842_; 
v___x_1842_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1816_);
v___y_1829_ = v___y_1837_;
v___y_1830_ = v___y_1838_;
v___y_1831_ = v___y_1840_;
v___y_1832_ = v___y_1839_;
v___y_1833_ = v___x_1842_;
goto v___jp_1828_;
}
else
{
v___y_1829_ = v___y_1837_;
v___y_1830_ = v___y_1838_;
v___y_1831_ = v___y_1840_;
v___y_1832_ = v___y_1839_;
v___y_1833_ = v___x_1841_;
goto v___jp_1828_;
}
}
v___jp_1843_:
{
uint8_t v___x_1847_; 
v___x_1847_ = l_Lean_Expr_Data_hasExprMVar(v___x_1813_);
if (v___x_1847_ == 0)
{
uint8_t v___x_1848_; 
v___x_1848_ = l_Lean_Expr_Data_hasExprMVar(v___x_1816_);
v___y_1837_ = v___y_1844_;
v___y_1838_ = v___y_1846_;
v___y_1839_ = v___y_1845_;
v___y_1840_ = v___x_1848_;
goto v___jp_1836_;
}
else
{
v___y_1837_ = v___y_1844_;
v___y_1838_ = v___y_1846_;
v___y_1839_ = v___y_1845_;
v___y_1840_ = v___x_1847_;
goto v___jp_1836_;
}
}
v___jp_1849_:
{
uint32_t v___x_1852_; uint32_t v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = 1;
v___x_1853_ = lean_uint32_add(v___y_1851_, v___x_1852_);
v___x_1854_ = l_Lean_Expr_Data_hasFVar(v___x_1813_);
if (v___x_1854_ == 0)
{
uint8_t v___x_1855_; 
v___x_1855_ = l_Lean_Expr_Data_hasFVar(v___x_1816_);
v___y_1844_ = v___y_1850_;
v___y_1845_ = v___x_1853_;
v___y_1846_ = v___x_1855_;
goto v___jp_1843_;
}
else
{
v___y_1844_ = v___y_1850_;
v___y_1845_ = v___x_1853_;
v___y_1846_ = v___x_1854_;
goto v___jp_1843_;
}
}
v___jp_1856_:
{
uint8_t v___x_1858_; uint32_t v___x_1859_; uint8_t v___x_1860_; uint32_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1858_ = l_Lean_Expr_Data_approxDepth(v___x_1813_);
v___x_1859_ = lean_uint8_to_uint32(v___x_1858_);
v___x_1860_ = l_Lean_Expr_Data_approxDepth(v___x_1816_);
v___x_1861_ = lean_uint8_to_uint32(v___x_1860_);
v___x_1862_ = lean_uint32_dec_le(v___x_1859_, v___x_1861_);
if (v___x_1862_ == 0)
{
v___y_1850_ = v___y_1857_;
v___y_1851_ = v___x_1859_;
goto v___jp_1849_;
}
else
{
v___y_1850_ = v___y_1857_;
v___y_1851_ = v___x_1861_;
goto v___jp_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1870_, lean_object* v_binderType_1871_, lean_object* v_body_1872_, lean_object* v_binderInfo_1873_){
_start:
{
uint8_t v_binderInfo_boxed_1874_; lean_object* v_res_1875_; 
v_binderInfo_boxed_1874_ = lean_unbox(v_binderInfo_1873_);
v_res_1875_ = l_Lean_Expr_lam___override(v_binderName_1870_, v_binderType_1871_, v_body_1872_, v_binderInfo_boxed_1874_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1876_, lean_object* v_binderType_1877_, lean_object* v_body_1878_, uint8_t v_binderInfo_1879_){
_start:
{
uint32_t v___x_1880_; uint64_t v___x_1881_; uint32_t v___x_1882_; uint32_t v___x_1883_; uint64_t v___x_1884_; uint32_t v___x_1885_; uint32_t v___x_1886_; uint8_t v___y_1888_; uint8_t v___y_1889_; uint8_t v___y_1890_; lean_object* v___y_1891_; uint32_t v___y_1892_; uint8_t v___y_1893_; uint8_t v___y_1897_; uint8_t v___y_1898_; lean_object* v___y_1899_; uint32_t v___y_1900_; uint8_t v___y_1901_; uint8_t v___y_1905_; lean_object* v___y_1906_; uint32_t v___y_1907_; uint8_t v___y_1908_; lean_object* v___y_1912_; uint32_t v___y_1913_; uint8_t v___y_1914_; lean_object* v___y_1918_; uint32_t v___y_1919_; lean_object* v___y_1925_; uint32_t v___x_1931_; lean_object* v___x_1932_; uint32_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1880_ = 31;
v___x_1881_ = lean_expr_data(v_binderType_1877_);
v___x_1882_ = lean_uint64_to_uint32(v___x_1881_);
v___x_1883_ = lean_uint32_mix_hash(v___x_1880_, v___x_1882_);
v___x_1884_ = lean_expr_data(v_body_1878_);
v___x_1885_ = lean_uint64_to_uint32(v___x_1884_);
v___x_1886_ = lean_uint32_mix_hash(v___x_1883_, v___x_1885_);
v___x_1931_ = l_Lean_Expr_Data_looseBVarRange(v___x_1881_);
v___x_1932_ = lean_uint32_to_nat(v___x_1931_);
v___x_1933_ = l_Lean_Expr_Data_looseBVarRange(v___x_1884_);
v___x_1934_ = lean_uint32_to_nat(v___x_1933_);
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = lean_nat_sub(v___x_1934_, v___x_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_nat_dec_le(v___x_1932_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_dec(v___x_1936_);
v___y_1925_ = v___x_1932_;
goto v___jp_1924_;
}
else
{
lean_dec(v___x_1932_);
v___y_1925_ = v___x_1936_;
goto v___jp_1924_;
}
v___jp_1887_:
{
uint64_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_expr_mk_data(v___x_1886_, v___y_1891_, v___y_1892_, v___y_1889_, v___y_1888_, v___y_1890_, v___y_1893_);
v___x_1895_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1895_, 0, v_binderName_1876_);
lean_ctor_set(v___x_1895_, 1, v_binderType_1877_);
lean_ctor_set(v___x_1895_, 2, v_body_1878_);
lean_ctor_set_uint64(v___x_1895_, sizeof(void*)*3, v___x_1894_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 8, v_binderInfo_1879_);
return v___x_1895_;
}
v___jp_1896_:
{
uint8_t v___x_1902_; 
v___x_1902_ = l_Lean_Expr_Data_hasLevelParam(v___x_1881_);
if (v___x_1902_ == 0)
{
uint8_t v___x_1903_; 
v___x_1903_ = l_Lean_Expr_Data_hasLevelParam(v___x_1884_);
v___y_1888_ = v___y_1897_;
v___y_1889_ = v___y_1898_;
v___y_1890_ = v___y_1901_;
v___y_1891_ = v___y_1899_;
v___y_1892_ = v___y_1900_;
v___y_1893_ = v___x_1903_;
goto v___jp_1887_;
}
else
{
v___y_1888_ = v___y_1897_;
v___y_1889_ = v___y_1898_;
v___y_1890_ = v___y_1901_;
v___y_1891_ = v___y_1899_;
v___y_1892_ = v___y_1900_;
v___y_1893_ = v___x_1902_;
goto v___jp_1887_;
}
}
v___jp_1904_:
{
uint8_t v___x_1909_; 
v___x_1909_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1881_);
if (v___x_1909_ == 0)
{
uint8_t v___x_1910_; 
v___x_1910_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1884_);
v___y_1897_ = v___y_1908_;
v___y_1898_ = v___y_1905_;
v___y_1899_ = v___y_1906_;
v___y_1900_ = v___y_1907_;
v___y_1901_ = v___x_1910_;
goto v___jp_1896_;
}
else
{
v___y_1897_ = v___y_1908_;
v___y_1898_ = v___y_1905_;
v___y_1899_ = v___y_1906_;
v___y_1900_ = v___y_1907_;
v___y_1901_ = v___x_1909_;
goto v___jp_1896_;
}
}
v___jp_1911_:
{
uint8_t v___x_1915_; 
v___x_1915_ = l_Lean_Expr_Data_hasExprMVar(v___x_1881_);
if (v___x_1915_ == 0)
{
uint8_t v___x_1916_; 
v___x_1916_ = l_Lean_Expr_Data_hasExprMVar(v___x_1884_);
v___y_1905_ = v___y_1914_;
v___y_1906_ = v___y_1912_;
v___y_1907_ = v___y_1913_;
v___y_1908_ = v___x_1916_;
goto v___jp_1904_;
}
else
{
v___y_1905_ = v___y_1914_;
v___y_1906_ = v___y_1912_;
v___y_1907_ = v___y_1913_;
v___y_1908_ = v___x_1915_;
goto v___jp_1904_;
}
}
v___jp_1917_:
{
uint32_t v___x_1920_; uint32_t v___x_1921_; uint8_t v___x_1922_; 
v___x_1920_ = 1;
v___x_1921_ = lean_uint32_add(v___y_1919_, v___x_1920_);
v___x_1922_ = l_Lean_Expr_Data_hasFVar(v___x_1881_);
if (v___x_1922_ == 0)
{
uint8_t v___x_1923_; 
v___x_1923_ = l_Lean_Expr_Data_hasFVar(v___x_1884_);
v___y_1912_ = v___y_1918_;
v___y_1913_ = v___x_1921_;
v___y_1914_ = v___x_1923_;
goto v___jp_1911_;
}
else
{
v___y_1912_ = v___y_1918_;
v___y_1913_ = v___x_1921_;
v___y_1914_ = v___x_1922_;
goto v___jp_1911_;
}
}
v___jp_1924_:
{
uint8_t v___x_1926_; uint32_t v___x_1927_; uint8_t v___x_1928_; uint32_t v___x_1929_; uint8_t v___x_1930_; 
v___x_1926_ = l_Lean_Expr_Data_approxDepth(v___x_1881_);
v___x_1927_ = lean_uint8_to_uint32(v___x_1926_);
v___x_1928_ = l_Lean_Expr_Data_approxDepth(v___x_1884_);
v___x_1929_ = lean_uint8_to_uint32(v___x_1928_);
v___x_1930_ = lean_uint32_dec_le(v___x_1927_, v___x_1929_);
if (v___x_1930_ == 0)
{
v___y_1918_ = v___y_1925_;
v___y_1919_ = v___x_1927_;
goto v___jp_1917_;
}
else
{
v___y_1918_ = v___y_1925_;
v___y_1919_ = v___x_1929_;
goto v___jp_1917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1938_, lean_object* v_binderType_1939_, lean_object* v_body_1940_, lean_object* v_binderInfo_1941_){
_start:
{
uint8_t v_binderInfo_boxed_1942_; lean_object* v_res_1943_; 
v_binderInfo_boxed_1942_ = lean_unbox(v_binderInfo_1941_);
v_res_1943_ = l_Lean_Expr_forallE___override(v_binderName_1938_, v_binderType_1939_, v_body_1940_, v_binderInfo_boxed_1942_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1944_, lean_object* v_type_1945_, lean_object* v_value_1946_, lean_object* v_body_1947_, uint8_t v_nondep_1948_){
_start:
{
lean_object* v___y_1950_; uint32_t v___y_1951_; uint8_t v___y_1952_; uint8_t v___y_1953_; uint8_t v___y_1954_; uint32_t v___y_1955_; uint8_t v___y_1956_; uint8_t v___x_1959_; uint64_t v___y_1961_; lean_object* v___y_1962_; uint32_t v___y_1963_; uint64_t v___y_1964_; uint64_t v___y_1965_; uint8_t v___y_1966_; uint8_t v___y_1967_; uint32_t v___y_1968_; uint8_t v___y_1969_; uint64_t v___y_1974_; lean_object* v___y_1975_; uint32_t v___y_1976_; uint64_t v___y_1977_; uint8_t v___y_1978_; uint64_t v___y_1979_; uint32_t v___y_1980_; uint8_t v___y_1981_; uint64_t v___y_1986_; lean_object* v___y_1987_; uint32_t v___y_1988_; uint64_t v___y_1989_; uint64_t v___y_1990_; uint32_t v___y_1991_; uint8_t v___y_1992_; uint64_t v___y_1997_; lean_object* v___y_1998_; uint32_t v___y_1999_; uint64_t v___y_2000_; uint64_t v___y_2001_; uint32_t v___y_2002_; uint64_t v___y_2009_; lean_object* v___y_2010_; uint32_t v___y_2011_; uint64_t v___y_2012_; uint64_t v___y_2013_; uint32_t v___y_2014_; uint64_t v___y_2019_; uint32_t v___y_2020_; uint64_t v___y_2021_; uint64_t v___y_2022_; lean_object* v___y_2023_; uint64_t v___y_2030_; uint32_t v___y_2031_; uint64_t v___y_2032_; uint64_t v___y_2033_; lean_object* v___y_2034_; uint32_t v___y_2041_; 
v___x_1959_ = 1;
if (v_nondep_1948_ == 0)
{
uint32_t v___x_2056_; 
v___x_2056_ = 37;
v___y_2041_ = v___x_2056_;
goto v___jp_2040_;
}
else
{
uint32_t v___x_2057_; 
v___x_2057_ = 41;
v___y_2041_ = v___x_2057_;
goto v___jp_2040_;
}
v___jp_1949_:
{
uint64_t v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_expr_mk_data(v___y_1951_, v___y_1950_, v___y_1955_, v___y_1952_, v___y_1954_, v___y_1953_, v___y_1956_);
v___x_1958_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1958_, 0, v_declName_1944_);
lean_ctor_set(v___x_1958_, 1, v_type_1945_);
lean_ctor_set(v___x_1958_, 2, v_value_1946_);
lean_ctor_set(v___x_1958_, 3, v_body_1947_);
lean_ctor_set_uint64(v___x_1958_, sizeof(void*)*4, v___x_1957_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*4 + 8, v_nondep_1948_);
return v___x_1958_;
}
v___jp_1960_:
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_Expr_Data_hasLevelParam(v___y_1964_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Lean_Expr_Data_hasLevelParam(v___y_1961_);
if (v___x_1971_ == 0)
{
uint8_t v___x_1972_; 
v___x_1972_ = l_Lean_Expr_Data_hasLevelParam(v___y_1965_);
v___y_1950_ = v___y_1962_;
v___y_1951_ = v___y_1963_;
v___y_1952_ = v___y_1966_;
v___y_1953_ = v___y_1969_;
v___y_1954_ = v___y_1967_;
v___y_1955_ = v___y_1968_;
v___y_1956_ = v___x_1972_;
goto v___jp_1949_;
}
else
{
v___y_1950_ = v___y_1962_;
v___y_1951_ = v___y_1963_;
v___y_1952_ = v___y_1966_;
v___y_1953_ = v___y_1969_;
v___y_1954_ = v___y_1967_;
v___y_1955_ = v___y_1968_;
v___y_1956_ = v___x_1959_;
goto v___jp_1949_;
}
}
else
{
v___y_1950_ = v___y_1962_;
v___y_1951_ = v___y_1963_;
v___y_1952_ = v___y_1966_;
v___y_1953_ = v___y_1969_;
v___y_1954_ = v___y_1967_;
v___y_1955_ = v___y_1968_;
v___y_1956_ = v___x_1959_;
goto v___jp_1949_;
}
}
v___jp_1973_:
{
uint8_t v___x_1982_; 
v___x_1982_ = l_Lean_Expr_Data_hasLevelMVar(v___y_1977_);
if (v___x_1982_ == 0)
{
uint8_t v___x_1983_; 
v___x_1983_ = l_Lean_Expr_Data_hasLevelMVar(v___y_1974_);
if (v___x_1983_ == 0)
{
uint8_t v___x_1984_; 
v___x_1984_ = l_Lean_Expr_Data_hasLevelMVar(v___y_1979_);
v___y_1961_ = v___y_1974_;
v___y_1962_ = v___y_1975_;
v___y_1963_ = v___y_1976_;
v___y_1964_ = v___y_1977_;
v___y_1965_ = v___y_1979_;
v___y_1966_ = v___y_1978_;
v___y_1967_ = v___y_1981_;
v___y_1968_ = v___y_1980_;
v___y_1969_ = v___x_1984_;
goto v___jp_1960_;
}
else
{
v___y_1961_ = v___y_1974_;
v___y_1962_ = v___y_1975_;
v___y_1963_ = v___y_1976_;
v___y_1964_ = v___y_1977_;
v___y_1965_ = v___y_1979_;
v___y_1966_ = v___y_1978_;
v___y_1967_ = v___y_1981_;
v___y_1968_ = v___y_1980_;
v___y_1969_ = v___x_1959_;
goto v___jp_1960_;
}
}
else
{
v___y_1961_ = v___y_1974_;
v___y_1962_ = v___y_1975_;
v___y_1963_ = v___y_1976_;
v___y_1964_ = v___y_1977_;
v___y_1965_ = v___y_1979_;
v___y_1966_ = v___y_1978_;
v___y_1967_ = v___y_1981_;
v___y_1968_ = v___y_1980_;
v___y_1969_ = v___x_1959_;
goto v___jp_1960_;
}
}
v___jp_1985_:
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_Expr_Data_hasExprMVar(v___y_1989_);
if (v___x_1993_ == 0)
{
uint8_t v___x_1994_; 
v___x_1994_ = l_Lean_Expr_Data_hasExprMVar(v___y_1986_);
if (v___x_1994_ == 0)
{
uint8_t v___x_1995_; 
v___x_1995_ = l_Lean_Expr_Data_hasExprMVar(v___y_1990_);
v___y_1974_ = v___y_1986_;
v___y_1975_ = v___y_1987_;
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1989_;
v___y_1978_ = v___y_1992_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___x_1995_;
goto v___jp_1973_;
}
else
{
v___y_1974_ = v___y_1986_;
v___y_1975_ = v___y_1987_;
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1989_;
v___y_1978_ = v___y_1992_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___x_1959_;
goto v___jp_1973_;
}
}
else
{
v___y_1974_ = v___y_1986_;
v___y_1975_ = v___y_1987_;
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1989_;
v___y_1978_ = v___y_1992_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___x_1959_;
goto v___jp_1973_;
}
}
v___jp_1996_:
{
uint32_t v___x_2003_; uint32_t v___x_2004_; uint8_t v___x_2005_; 
v___x_2003_ = 1;
v___x_2004_ = lean_uint32_add(v___y_2002_, v___x_2003_);
v___x_2005_ = l_Lean_Expr_Data_hasFVar(v___y_2000_);
if (v___x_2005_ == 0)
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lean_Expr_Data_hasFVar(v___y_1997_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; 
v___x_2007_ = l_Lean_Expr_Data_hasFVar(v___y_2001_);
v___y_1986_ = v___y_1997_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1999_;
v___y_1989_ = v___y_2000_;
v___y_1990_ = v___y_2001_;
v___y_1991_ = v___x_2004_;
v___y_1992_ = v___x_2007_;
goto v___jp_1985_;
}
else
{
v___y_1986_ = v___y_1997_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1999_;
v___y_1989_ = v___y_2000_;
v___y_1990_ = v___y_2001_;
v___y_1991_ = v___x_2004_;
v___y_1992_ = v___x_1959_;
goto v___jp_1985_;
}
}
else
{
v___y_1986_ = v___y_1997_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1999_;
v___y_1989_ = v___y_2000_;
v___y_1990_ = v___y_2001_;
v___y_1991_ = v___x_2004_;
v___y_1992_ = v___x_1959_;
goto v___jp_1985_;
}
}
v___jp_2008_:
{
uint8_t v___x_2015_; uint32_t v___x_2016_; uint8_t v___x_2017_; 
v___x_2015_ = l_Lean_Expr_Data_approxDepth(v___y_2013_);
v___x_2016_ = lean_uint8_to_uint32(v___x_2015_);
v___x_2017_ = lean_uint32_dec_le(v___y_2014_, v___x_2016_);
if (v___x_2017_ == 0)
{
v___y_1997_ = v___y_2009_;
v___y_1998_ = v___y_2010_;
v___y_1999_ = v___y_2011_;
v___y_2000_ = v___y_2012_;
v___y_2001_ = v___y_2013_;
v___y_2002_ = v___y_2014_;
goto v___jp_1996_;
}
else
{
v___y_1997_ = v___y_2009_;
v___y_1998_ = v___y_2010_;
v___y_1999_ = v___y_2011_;
v___y_2000_ = v___y_2012_;
v___y_2001_ = v___y_2013_;
v___y_2002_ = v___x_2016_;
goto v___jp_1996_;
}
}
v___jp_2018_:
{
uint8_t v___x_2024_; uint32_t v___x_2025_; uint8_t v___x_2026_; uint32_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2024_ = l_Lean_Expr_Data_approxDepth(v___y_2021_);
v___x_2025_ = lean_uint8_to_uint32(v___x_2024_);
v___x_2026_ = l_Lean_Expr_Data_approxDepth(v___y_2019_);
v___x_2027_ = lean_uint8_to_uint32(v___x_2026_);
v___x_2028_ = lean_uint32_dec_le(v___x_2025_, v___x_2027_);
if (v___x_2028_ == 0)
{
v___y_2009_ = v___y_2019_;
v___y_2010_ = v___y_2023_;
v___y_2011_ = v___y_2020_;
v___y_2012_ = v___y_2021_;
v___y_2013_ = v___y_2022_;
v___y_2014_ = v___x_2025_;
goto v___jp_2008_;
}
else
{
v___y_2009_ = v___y_2019_;
v___y_2010_ = v___y_2023_;
v___y_2011_ = v___y_2020_;
v___y_2012_ = v___y_2021_;
v___y_2013_ = v___y_2022_;
v___y_2014_ = v___x_2027_;
goto v___jp_2008_;
}
}
v___jp_2029_:
{
uint32_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2035_ = l_Lean_Expr_Data_looseBVarRange(v___y_2033_);
v___x_2036_ = lean_uint32_to_nat(v___x_2035_);
v___x_2037_ = lean_unsigned_to_nat(1u);
v___x_2038_ = lean_nat_sub(v___x_2036_, v___x_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_nat_dec_le(v___y_2034_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_dec(v___x_2038_);
v___y_2019_ = v___y_2030_;
v___y_2020_ = v___y_2031_;
v___y_2021_ = v___y_2032_;
v___y_2022_ = v___y_2033_;
v___y_2023_ = v___y_2034_;
goto v___jp_2018_;
}
else
{
lean_dec(v___y_2034_);
v___y_2019_ = v___y_2030_;
v___y_2020_ = v___y_2031_;
v___y_2021_ = v___y_2032_;
v___y_2022_ = v___y_2033_;
v___y_2023_ = v___x_2038_;
goto v___jp_2018_;
}
}
v___jp_2040_:
{
uint64_t v___x_2042_; uint32_t v___x_2043_; uint32_t v___x_2044_; uint64_t v___x_2045_; uint32_t v___x_2046_; uint32_t v___x_2047_; uint64_t v___x_2048_; uint32_t v___x_2049_; uint32_t v___x_2050_; uint32_t v___x_2051_; lean_object* v___x_2052_; uint32_t v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2042_ = lean_expr_data(v_type_1945_);
v___x_2043_ = lean_uint64_to_uint32(v___x_2042_);
v___x_2044_ = lean_uint32_mix_hash(v___y_2041_, v___x_2043_);
v___x_2045_ = lean_expr_data(v_value_1946_);
v___x_2046_ = lean_uint64_to_uint32(v___x_2045_);
v___x_2047_ = lean_uint32_mix_hash(v___x_2044_, v___x_2046_);
v___x_2048_ = lean_expr_data(v_body_1947_);
v___x_2049_ = lean_uint64_to_uint32(v___x_2048_);
v___x_2050_ = lean_uint32_mix_hash(v___x_2047_, v___x_2049_);
v___x_2051_ = l_Lean_Expr_Data_looseBVarRange(v___x_2042_);
v___x_2052_ = lean_uint32_to_nat(v___x_2051_);
v___x_2053_ = l_Lean_Expr_Data_looseBVarRange(v___x_2045_);
v___x_2054_ = lean_uint32_to_nat(v___x_2053_);
v___x_2055_ = lean_nat_dec_le(v___x_2052_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_dec(v___x_2054_);
v___y_2030_ = v___x_2045_;
v___y_2031_ = v___x_2050_;
v___y_2032_ = v___x_2042_;
v___y_2033_ = v___x_2048_;
v___y_2034_ = v___x_2052_;
goto v___jp_2029_;
}
else
{
lean_dec(v___x_2052_);
v___y_2030_ = v___x_2045_;
v___y_2031_ = v___x_2050_;
v___y_2032_ = v___x_2042_;
v___y_2033_ = v___x_2048_;
v___y_2034_ = v___x_2054_;
goto v___jp_2029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2058_, lean_object* v_type_2059_, lean_object* v_value_2060_, lean_object* v_body_2061_, lean_object* v_nondep_2062_){
_start:
{
uint8_t v_nondep_boxed_2063_; lean_object* v_res_2064_; 
v_nondep_boxed_2063_ = lean_unbox(v_nondep_2062_);
v_res_2064_ = l_Lean_Expr_letE___override(v_declName_2058_, v_type_2059_, v_value_2060_, v_body_2061_, v_nondep_boxed_2063_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2065_){
_start:
{
uint64_t v___x_2066_; uint64_t v___x_2067_; uint64_t v___x_2068_; uint32_t v___x_2069_; lean_object* v___x_2070_; uint32_t v___x_2071_; uint8_t v___x_2072_; uint64_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2066_ = 3ULL;
v___x_2067_ = l_Lean_Literal_hash(v_a_2065_);
v___x_2068_ = lean_uint64_mix_hash(v___x_2066_, v___x_2067_);
v___x_2069_ = lean_uint64_to_uint32(v___x_2068_);
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = 0;
v___x_2072_ = 0;
v___x_2073_ = lean_expr_mk_data(v___x_2069_, v___x_2070_, v___x_2071_, v___x_2072_, v___x_2072_, v___x_2072_, v___x_2072_);
v___x_2074_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2074_, 0, v_a_2065_);
lean_ctor_set_uint64(v___x_2074_, sizeof(void*)*1, v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2075_, lean_object* v_expr_2076_){
_start:
{
uint32_t v___x_2077_; uint64_t v___x_2078_; uint32_t v___x_2079_; uint32_t v___x_2080_; uint32_t v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; uint32_t v___x_2084_; uint32_t v___x_2085_; uint32_t v___x_2086_; uint8_t v___x_2087_; uint8_t v___x_2088_; uint8_t v___x_2089_; uint8_t v___x_2090_; uint64_t v___x_2091_; lean_object* v___x_2092_; 
v___x_2077_ = 19;
v___x_2078_ = lean_expr_data(v_expr_2076_);
v___x_2079_ = lean_uint64_to_uint32(v___x_2078_);
v___x_2080_ = lean_uint32_mix_hash(v___x_2077_, v___x_2079_);
v___x_2081_ = l_Lean_Expr_Data_looseBVarRange(v___x_2078_);
v___x_2082_ = lean_uint32_to_nat(v___x_2081_);
v___x_2083_ = l_Lean_Expr_Data_approxDepth(v___x_2078_);
v___x_2084_ = lean_uint8_to_uint32(v___x_2083_);
v___x_2085_ = 1;
v___x_2086_ = lean_uint32_add(v___x_2084_, v___x_2085_);
v___x_2087_ = l_Lean_Expr_Data_hasFVar(v___x_2078_);
v___x_2088_ = l_Lean_Expr_Data_hasExprMVar(v___x_2078_);
v___x_2089_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2078_);
v___x_2090_ = l_Lean_Expr_Data_hasLevelParam(v___x_2078_);
v___x_2091_ = lean_expr_mk_data(v___x_2080_, v___x_2082_, v___x_2086_, v___x_2087_, v___x_2088_, v___x_2089_, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2092_, 0, v_data_2075_);
lean_ctor_set(v___x_2092_, 1, v_expr_2076_);
lean_ctor_set_uint64(v___x_2092_, sizeof(void*)*2, v___x_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2093_, lean_object* v_idx_2094_, lean_object* v_struct_2095_){
_start:
{
uint64_t v___x_2096_; uint64_t v___y_2098_; 
v___x_2096_ = 23ULL;
if (lean_obj_tag(v_typeName_2093_) == 0)
{
uint64_t v___x_2118_; 
v___x_2118_ = 1723ULL;
v___y_2098_ = v___x_2118_;
goto v___jp_2097_;
}
else
{
uint64_t v_hash_2119_; 
v_hash_2119_ = lean_ctor_get_uint64(v_typeName_2093_, sizeof(void*)*2);
v___y_2098_ = v_hash_2119_;
goto v___jp_2097_;
}
v___jp_2097_:
{
uint64_t v___x_2099_; uint64_t v___x_2100_; uint64_t v___x_2101_; uint32_t v___x_2102_; uint64_t v___x_2103_; uint32_t v___x_2104_; uint32_t v___x_2105_; uint32_t v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; uint32_t v___x_2109_; uint32_t v___x_2110_; uint32_t v___x_2111_; uint8_t v___x_2112_; uint8_t v___x_2113_; uint8_t v___x_2114_; uint8_t v___x_2115_; uint64_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2099_ = lean_uint64_of_nat(v_idx_2094_);
v___x_2100_ = lean_uint64_mix_hash(v___y_2098_, v___x_2099_);
v___x_2101_ = lean_uint64_mix_hash(v___x_2096_, v___x_2100_);
v___x_2102_ = lean_uint64_to_uint32(v___x_2101_);
v___x_2103_ = lean_expr_data(v_struct_2095_);
v___x_2104_ = lean_uint64_to_uint32(v___x_2103_);
v___x_2105_ = lean_uint32_mix_hash(v___x_2102_, v___x_2104_);
v___x_2106_ = l_Lean_Expr_Data_looseBVarRange(v___x_2103_);
v___x_2107_ = lean_uint32_to_nat(v___x_2106_);
v___x_2108_ = l_Lean_Expr_Data_approxDepth(v___x_2103_);
v___x_2109_ = lean_uint8_to_uint32(v___x_2108_);
v___x_2110_ = 1;
v___x_2111_ = lean_uint32_add(v___x_2109_, v___x_2110_);
v___x_2112_ = l_Lean_Expr_Data_hasFVar(v___x_2103_);
v___x_2113_ = l_Lean_Expr_Data_hasExprMVar(v___x_2103_);
v___x_2114_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2103_);
v___x_2115_ = l_Lean_Expr_Data_hasLevelParam(v___x_2103_);
v___x_2116_ = lean_expr_mk_data(v___x_2105_, v___x_2107_, v___x_2111_, v___x_2112_, v___x_2113_, v___x_2114_, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2117_, 0, v_typeName_2093_);
lean_ctor_set(v___x_2117_, 1, v_idx_2094_);
lean_ctor_set(v___x_2117_, 2, v_struct_2095_);
lean_ctor_set_uint64(v___x_2117_, sizeof(void*)*3, v___x_2116_);
return v___x_2117_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2120_){
_start:
{
if (lean_obj_tag(v_x_2120_) == 0)
{
uint8_t v___x_2121_; 
v___x_2121_ = 0;
return v___x_2121_;
}
else
{
lean_object* v_head_2122_; lean_object* v_tail_2123_; uint8_t v___x_2124_; 
v_head_2122_ = lean_ctor_get(v_x_2120_, 0);
v_tail_2123_ = lean_ctor_get(v_x_2120_, 1);
v___x_2124_ = l_Lean_Level_hasMVar(v_head_2122_);
if (v___x_2124_ == 0)
{
v_x_2120_ = v_tail_2123_;
goto _start;
}
else
{
return v___x_2124_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2126_){
_start:
{
uint8_t v_res_2127_; lean_object* v_r_2128_; 
v_res_2127_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2126_);
lean_dec(v_x_2126_);
v_r_2128_ = lean_box(v_res_2127_);
return v_r_2128_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2129_){
_start:
{
if (lean_obj_tag(v_x_2129_) == 0)
{
uint8_t v___x_2130_; 
v___x_2130_ = 0;
return v___x_2130_;
}
else
{
lean_object* v_head_2131_; lean_object* v_tail_2132_; uint8_t v___x_2133_; 
v_head_2131_ = lean_ctor_get(v_x_2129_, 0);
v_tail_2132_ = lean_ctor_get(v_x_2129_, 1);
v___x_2133_ = l_Lean_Level_hasParam(v_head_2131_);
if (v___x_2133_ == 0)
{
v_x_2129_ = v_tail_2132_;
goto _start;
}
else
{
return v___x_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2135_){
_start:
{
uint8_t v_res_2136_; lean_object* v_r_2137_; 
v_res_2136_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2135_);
lean_dec(v_x_2135_);
v_r_2137_ = lean_box(v_res_2136_);
return v_r_2137_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2138_, lean_object* v_x_2139_){
_start:
{
if (lean_obj_tag(v_x_2139_) == 0)
{
return v_x_2138_;
}
else
{
lean_object* v_head_2140_; lean_object* v_tail_2141_; uint64_t v___x_2142_; uint64_t v___x_2143_; 
v_head_2140_ = lean_ctor_get(v_x_2139_, 0);
v_tail_2141_ = lean_ctor_get(v_x_2139_, 1);
v___x_2142_ = l_Lean_Level_hash(v_head_2140_);
v___x_2143_ = lean_uint64_mix_hash(v_x_2138_, v___x_2142_);
v_x_2138_ = v___x_2143_;
v_x_2139_ = v_tail_2141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2145_, lean_object* v_x_2146_){
_start:
{
uint64_t v_x_1721__boxed_2147_; uint64_t v_res_2148_; lean_object* v_r_2149_; 
v_x_1721__boxed_2147_ = lean_unbox_uint64(v_x_2145_);
lean_dec_ref(v_x_2145_);
v_res_2148_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1721__boxed_2147_, v_x_2146_);
lean_dec(v_x_2146_);
v_r_2149_ = lean_box_uint64(v_res_2148_);
return v_r_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2150_, lean_object* v_us_2151_){
_start:
{
uint64_t v___x_2152_; uint64_t v___y_2154_; 
v___x_2152_ = 5ULL;
if (lean_obj_tag(v_declName_2150_) == 0)
{
uint64_t v___x_2167_; 
v___x_2167_ = 1723ULL;
v___y_2154_ = v___x_2167_;
goto v___jp_2153_;
}
else
{
uint64_t v_hash_2168_; 
v_hash_2168_ = lean_ctor_get_uint64(v_declName_2150_, sizeof(void*)*2);
v___y_2154_ = v_hash_2168_;
goto v___jp_2153_;
}
v___jp_2153_:
{
uint64_t v___x_2155_; uint64_t v___x_2156_; uint64_t v___x_2157_; uint64_t v___x_2158_; uint32_t v___x_2159_; lean_object* v___x_2160_; uint32_t v___x_2161_; uint8_t v___x_2162_; uint8_t v___x_2163_; uint8_t v___x_2164_; uint64_t v___x_2165_; lean_object* v___x_2166_; 
v___x_2155_ = 7ULL;
v___x_2156_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2155_, v_us_2151_);
v___x_2157_ = lean_uint64_mix_hash(v___y_2154_, v___x_2156_);
v___x_2158_ = lean_uint64_mix_hash(v___x_2152_, v___x_2157_);
v___x_2159_ = lean_uint64_to_uint32(v___x_2158_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = 0;
v___x_2162_ = 0;
v___x_2163_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2151_);
v___x_2164_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2151_);
v___x_2165_ = lean_expr_mk_data(v___x_2159_, v___x_2160_, v___x_2161_, v___x_2162_, v___x_2162_, v___x_2163_, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2166_, 0, v_declName_2150_);
lean_ctor_set(v___x_2166_, 1, v_us_2151_);
lean_ctor_set_uint64(v___x_2166_, sizeof(void*)*2, v___x_2165_);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2169_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = l_Lean_instReprLevel_repr(v___y_2169_, v___x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
if (lean_obj_tag(v_x_2174_) == 0)
{
lean_dec(v_x_2172_);
return v_x_2173_;
}
else
{
lean_object* v_head_2175_; lean_object* v_tail_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2187_; 
v_head_2175_ = lean_ctor_get(v_x_2174_, 0);
v_tail_2176_ = lean_ctor_get(v_x_2174_, 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_x_2174_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2178_ = v_x_2174_;
v_isShared_2179_ = v_isSharedCheck_2187_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_tail_2176_);
lean_inc(v_head_2175_);
lean_dec(v_x_2174_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2187_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
lean_inc(v_x_2172_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set_tag(v___x_2178_, 5);
lean_ctor_set(v___x_2178_, 1, v_x_2172_);
lean_ctor_set(v___x_2178_, 0, v_x_2173_);
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_x_2173_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_x_2172_);
v___x_2181_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = l_Lean_instReprLevel_repr(v_head_2175_, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2181_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v_x_2173_ = v___x_2184_;
v_x_2174_ = v_tail_2176_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2188_, lean_object* v_x_2189_, lean_object* v_x_2190_){
_start:
{
if (lean_obj_tag(v_x_2190_) == 0)
{
lean_dec(v_x_2188_);
return v_x_2189_;
}
else
{
lean_object* v_head_2191_; lean_object* v_tail_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2203_; 
v_head_2191_ = lean_ctor_get(v_x_2190_, 0);
v_tail_2192_ = lean_ctor_get(v_x_2190_, 1);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_x_2190_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2194_ = v_x_2190_;
v_isShared_2195_ = v_isSharedCheck_2203_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_tail_2192_);
lean_inc(v_head_2191_);
lean_dec(v_x_2190_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2203_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
lean_inc(v_x_2188_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set_tag(v___x_2194_, 5);
lean_ctor_set(v___x_2194_, 1, v_x_2188_);
lean_ctor_set(v___x_2194_, 0, v_x_2189_);
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_x_2189_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_x_2188_);
v___x_2197_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = l_Lean_instReprLevel_repr(v_head_2191_, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2197_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2188_, v___x_2200_, v_tail_2192_);
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2204_, lean_object* v_x_2205_){
_start:
{
if (lean_obj_tag(v_x_2204_) == 0)
{
lean_object* v___x_2206_; 
lean_dec(v_x_2205_);
v___x_2206_ = lean_box(0);
return v___x_2206_;
}
else
{
lean_object* v_tail_2207_; 
v_tail_2207_ = lean_ctor_get(v_x_2204_, 1);
if (lean_obj_tag(v_tail_2207_) == 0)
{
lean_object* v_head_2208_; lean_object* v___x_2209_; 
lean_dec(v_x_2205_);
v_head_2208_ = lean_ctor_get(v_x_2204_, 0);
lean_inc(v_head_2208_);
lean_dec_ref_known(v_x_2204_, 2);
v___x_2209_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2208_);
return v___x_2209_;
}
else
{
lean_object* v_head_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_inc(v_tail_2207_);
v_head_2210_ = lean_ctor_get(v_x_2204_, 0);
lean_inc(v_head_2210_);
lean_dec_ref_known(v_x_2204_, 2);
v___x_2211_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2210_);
v___x_2212_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2205_, v___x_2211_, v_tail_2207_);
return v___x_2212_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2225_ = lean_string_length(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2227_ = lean_nat_to_int(v___x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2232_){
_start:
{
if (lean_obj_tag(v_a_2232_) == 0)
{
lean_object* v___x_2233_; 
v___x_2233_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2233_;
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; 
v___x_2234_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2235_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2232_, v___x_2234_);
v___x_2236_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2237_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v___x_2235_);
v___x_2239_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2236_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = 0;
v___x_2243_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set_uint8(v___x_2243_, sizeof(void*)*1, v___x_2242_);
return v___x_2243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2316_, lean_object* v_prec_2317_){
_start:
{
switch(lean_obj_tag(v_x_2316_))
{
case 0:
{
lean_object* v_deBruijnIndex_2318_; lean_object* v___y_2320_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v_deBruijnIndex_2318_ = lean_ctor_get(v_x_2316_, 0);
lean_inc(v_deBruijnIndex_2318_);
lean_dec_ref_known(v_x_2316_, 1);
v___x_2329_ = lean_unsigned_to_nat(1024u);
v___x_2330_ = lean_nat_dec_le(v___x_2329_, v_prec_2317_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2320_ = v___x_2331_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2320_ = v___x_2332_;
goto v___jp_2319_;
}
v___jp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2321_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2322_ = l_Nat_reprFast(v_deBruijnIndex_2318_);
v___x_2323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
v___x_2324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2321_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
lean_inc(v___y_2320_);
v___x_2325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___y_2320_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = 0;
v___x_2327_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*1, v___x_2326_);
v___x_2328_ = l_Repr_addAppParen(v___x_2327_, v_prec_2317_);
return v___x_2328_;
}
}
case 1:
{
lean_object* v_fvarId_2333_; lean_object* v___y_2335_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v_fvarId_2333_ = lean_ctor_get(v_x_2316_, 0);
lean_inc(v_fvarId_2333_);
lean_dec_ref_known(v_x_2316_, 1);
v___x_2344_ = lean_unsigned_to_nat(1024u);
v___x_2345_ = lean_nat_dec_le(v___x_2344_, v_prec_2317_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2335_ = v___x_2346_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2347_; 
v___x_2347_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2335_ = v___x_2347_;
goto v___jp_2334_;
}
v___jp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2336_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2337_ = lean_unsigned_to_nat(1024u);
v___x_2338_ = l_Lean_Name_reprPrec(v_fvarId_2333_, v___x_2337_);
v___x_2339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2336_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
lean_inc(v___y_2335_);
v___x_2340_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___y_2335_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = 0;
v___x_2342_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*1, v___x_2341_);
v___x_2343_ = l_Repr_addAppParen(v___x_2342_, v_prec_2317_);
return v___x_2343_;
}
}
case 2:
{
lean_object* v_mvarId_2348_; lean_object* v___y_2350_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v_mvarId_2348_ = lean_ctor_get(v_x_2316_, 0);
lean_inc(v_mvarId_2348_);
lean_dec_ref_known(v_x_2316_, 1);
v___x_2359_ = lean_unsigned_to_nat(1024u);
v___x_2360_ = lean_nat_dec_le(v___x_2359_, v_prec_2317_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2350_ = v___x_2361_;
goto v___jp_2349_;
}
else
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2350_ = v___x_2362_;
goto v___jp_2349_;
}
v___jp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2351_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2352_ = lean_unsigned_to_nat(1024u);
v___x_2353_ = l_Lean_Name_reprPrec(v_mvarId_2348_, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2351_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
lean_inc(v___y_2350_);
v___x_2355_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___y_2350_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = 0;
v___x_2357_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*1, v___x_2356_);
v___x_2358_ = l_Repr_addAppParen(v___x_2357_, v_prec_2317_);
return v___x_2358_;
}
}
case 3:
{
lean_object* v_u_2363_; lean_object* v___y_2365_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_u_2363_ = lean_ctor_get(v_x_2316_, 0);
lean_inc(v_u_2363_);
lean_dec_ref_known(v_x_2316_, 1);
v___x_2374_ = lean_unsigned_to_nat(1024u);
v___x_2375_ = lean_nat_dec_le(v___x_2374_, v_prec_2317_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2365_ = v___x_2376_;
goto v___jp_2364_;
}
else
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2365_ = v___x_2377_;
goto v___jp_2364_;
}
v___jp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2366_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2367_ = lean_unsigned_to_nat(1024u);
v___x_2368_ = l_Lean_instReprLevel_repr(v_u_2363_, v___x_2367_);
v___x_2369_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2366_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
lean_inc(v___y_2365_);
v___x_2370_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___y_2365_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = 0;
v___x_2372_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set_uint8(v___x_2372_, sizeof(void*)*1, v___x_2371_);
v___x_2373_ = l_Repr_addAppParen(v___x_2372_, v_prec_2317_);
return v___x_2373_;
}
}
case 4:
{
lean_object* v_declName_2378_; lean_object* v_us_2379_; lean_object* v___y_2381_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v_declName_2378_ = lean_ctor_get(v_x_2316_, 0);
lean_inc(v_declName_2378_);
v_us_2379_ = lean_ctor_get(v_x_2316_, 1);
lean_inc(v_us_2379_);
lean_dec_ref_known(v_x_2316_, 2);
v___x_2394_ = lean_unsigned_to_nat(1024u);
v___x_2395_ = lean_nat_dec_le(v___x_2394_, v_prec_2317_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2381_ = v___x_2396_;
goto v___jp_2380_;
}
else
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2381_ = v___x_2397_;
goto v___jp_2380_;
}
v___jp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2382_ = lean_box(1);
v___x_2383_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2384_ = lean_unsigned_to_nat(1024u);
v___x_2385_ = l_Lean_Name_reprPrec(v_declName_2378_, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2383_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v___x_2382_);
v___x_2388_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2379_);
v___x_2389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
lean_inc(v___y_2381_);
v___x_2390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___y_2381_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = 0;
v___x_2392_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*1, v___x_2391_);
v___x_2393_ = l_Repr_addAppParen(v___x_2392_, v_prec_2317_);
return v___x_2393_;
}
}
case 5:
{
lean_object* v_fn_2398_; lean_object* v_arg_2399_; lean_object* v___x_2400_; lean_object* v___y_2402_; uint8_t v___x_2414_; 
v_fn_2398_ = lean_ctor_get(v_x_2316_, 0);
lean_inc_ref(v_fn_2398_);
v_arg_2399_ = lean_ctor_get(v_x_2316_, 1);
lean_inc_ref(v_arg_2399_);
lean_dec_ref_known(v_x_2316_, 2);
v___x_2400_ = lean_unsigned_to_nat(1024u);
v___x_2414_ = lean_nat_dec_le(v___x_2400_, v_prec_2317_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2402_ = v___x_2415_;
goto v___jp_2401_;
}
else
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2402_ = v___x_2416_;
goto v___jp_2401_;
}
v___jp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2403_ = lean_box(1);
v___x_2404_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2405_ = l_Lean_instReprExpr_repr(v_fn_2398_, v___x_2400_);
v___x_2406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v___x_2403_);
v___x_2408_ = l_Lean_instReprExpr_repr(v_arg_2399_, v___x_2400_);
v___x_2409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
lean_inc(v___y_2402_);
v___x_2410_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___y_2402_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = 0;
v___x_2412_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*1, v___x_2411_);
v___x_2413_ = l_Repr_addAppParen(v___x_2412_, v_prec_2317_);
return v___x_2413_;
}
}
case 6:
{
lean_object* v_binderName_2417_; lean_object* v_binderType_2418_; lean_object* v_body_2419_; uint8_t v_binderInfo_2420_; lean_object* v___x_2421_; lean_object* v___y_2423_; uint8_t v___x_2441_; 
v_binderName_2417_ = lean_ctor_get(v_x_2316_, 0);
lean_inc(v_binderName_2417_);
v_binderType_2418_ = lean_ctor_get(v_x_2316_, 1);
lean_inc_ref(v_binderType_2418_);
v_body_2419_ = lean_ctor_get(v_x_2316_, 2);
lean_inc_ref(v_body_2419_);
v_binderInfo_2420_ = lean_ctor_get_uint8(v_x_2316_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2316_, 3);
v___x_2421_ = lean_unsigned_to_nat(1024u);
v___x_2441_ = lean_nat_dec_le(v___x_2421_, v_prec_2317_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2423_ = v___x_2442_;
goto v___jp_2422_;
}
else
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2423_ = v___x_2443_;
goto v___jp_2422_;
}
v___jp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2424_ = lean_box(1);
v___x_2425_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2426_ = l_Lean_Name_reprPrec(v_binderName_2417_, v___x_2421_);
v___x_2427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___x_2424_);
v___x_2429_ = l_Lean_instReprExpr_repr(v_binderType_2418_, v___x_2421_);
v___x_2430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2428_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v___x_2424_);
v___x_2432_ = l_Lean_instReprExpr_repr(v_body_2419_, v___x_2421_);
v___x_2433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v___x_2424_);
v___x_2435_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2420_, v___x_2421_);
v___x_2436_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
lean_inc(v___y_2423_);
v___x_2437_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___y_2423_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = 0;
v___x_2439_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set_uint8(v___x_2439_, sizeof(void*)*1, v___x_2438_);
v___x_2440_ = l_Repr_addAppParen(v___x_2439_, v_prec_2317_);
return v___x_2440_;
}
}
case 7:
{
lean_object* v_binderName_2444_; lean_object* v_binderType_2445_; lean_object* v_body_2446_; uint8_t v_binderInfo_2447_; lean_object* v___x_2448_; lean_object* v___y_2450_; uint8_t v___x_2468_; 
v_binderName_2444_ = lean_ctor_get(v_x_2316_, 0);
lean_inc(v_binderName_2444_);
v_binderType_2445_ = lean_ctor_get(v_x_2316_, 1);
lean_inc_ref(v_binderType_2445_);
v_body_2446_ = lean_ctor_get(v_x_2316_, 2);
lean_inc_ref(v_body_2446_);
v_binderInfo_2447_ = lean_ctor_get_uint8(v_x_2316_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2316_, 3);
v___x_2448_ = lean_unsigned_to_nat(1024u);
v___x_2468_ = lean_nat_dec_le(v___x_2448_, v_prec_2317_);
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
v___x_2452_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
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
v___x_2467_ = l_Repr_addAppParen(v___x_2466_, v_prec_2317_);
return v___x_2467_;
}
}
case 8:
{
lean_object* v_declName_2471_; lean_object* v_type_2472_; lean_object* v_value_2473_; lean_object* v_body_2474_; uint8_t v_nondep_2475_; lean_object* v___x_2476_; lean_object* v___y_2478_; uint8_t v___x_2499_; 
v_declName_2471_ = lean_ctor_get(v_x_2316_, 0);
lean_inc(v_declName_2471_);
v_type_2472_ = lean_ctor_get(v_x_2316_, 1);
lean_inc_ref(v_type_2472_);
v_value_2473_ = lean_ctor_get(v_x_2316_, 2);
lean_inc_ref(v_value_2473_);
v_body_2474_ = lean_ctor_get(v_x_2316_, 3);
lean_inc_ref(v_body_2474_);
v_nondep_2475_ = lean_ctor_get_uint8(v_x_2316_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_2316_, 4);
v___x_2476_ = lean_unsigned_to_nat(1024u);
v___x_2499_ = lean_nat_dec_le(v___x_2476_, v_prec_2317_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2478_ = v___x_2500_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2478_ = v___x_2501_;
goto v___jp_2477_;
}
v___jp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2479_ = lean_box(1);
v___x_2480_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2481_ = l_Lean_Name_reprPrec(v_declName_2471_, v___x_2476_);
v___x_2482_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
lean_ctor_set(v___x_2483_, 1, v___x_2479_);
v___x_2484_ = l_Lean_instReprExpr_repr(v_type_2472_, v___x_2476_);
v___x_2485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_2479_);
v___x_2487_ = l_Lean_instReprExpr_repr(v_value_2473_, v___x_2476_);
v___x_2488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
lean_ctor_set(v___x_2489_, 1, v___x_2479_);
v___x_2490_ = l_Lean_instReprExpr_repr(v_body_2474_, v___x_2476_);
v___x_2491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2489_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
lean_ctor_set(v___x_2492_, 1, v___x_2479_);
v___x_2493_ = l_Bool_repr___redArg(v_nondep_2475_);
v___x_2494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
lean_inc(v___y_2478_);
v___x_2495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___y_2478_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = 0;
v___x_2497_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2497_, 0, v___x_2495_);
lean_ctor_set_uint8(v___x_2497_, sizeof(void*)*1, v___x_2496_);
v___x_2498_ = l_Repr_addAppParen(v___x_2497_, v_prec_2317_);
return v___x_2498_;
}
}
case 9:
{
lean_object* v_a_2502_; lean_object* v___y_2504_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v_a_2502_ = lean_ctor_get(v_x_2316_, 0);
lean_inc_ref(v_a_2502_);
lean_dec_ref_known(v_x_2316_, 1);
v___x_2513_ = lean_unsigned_to_nat(1024u);
v___x_2514_ = lean_nat_dec_le(v___x_2513_, v_prec_2317_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2504_ = v___x_2515_;
goto v___jp_2503_;
}
else
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2504_ = v___x_2516_;
goto v___jp_2503_;
}
v___jp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2505_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2506_ = lean_unsigned_to_nat(1024u);
v___x_2507_ = l_Lean_instReprLiteral_repr(v_a_2502_, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2505_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
lean_inc(v___y_2504_);
v___x_2509_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___y_2504_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = 0;
v___x_2511_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*1, v___x_2510_);
v___x_2512_ = l_Repr_addAppParen(v___x_2511_, v_prec_2317_);
return v___x_2512_;
}
}
case 10:
{
lean_object* v_data_2517_; lean_object* v_expr_2518_; lean_object* v___x_2519_; lean_object* v___y_2521_; uint8_t v___x_2533_; 
v_data_2517_ = lean_ctor_get(v_x_2316_, 0);
lean_inc(v_data_2517_);
v_expr_2518_ = lean_ctor_get(v_x_2316_, 1);
lean_inc_ref(v_expr_2518_);
lean_dec_ref_known(v_x_2316_, 2);
v___x_2519_ = lean_unsigned_to_nat(1024u);
v___x_2533_ = lean_nat_dec_le(v___x_2519_, v_prec_2317_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2521_ = v___x_2534_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2521_ = v___x_2535_;
goto v___jp_2520_;
}
v___jp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2522_ = lean_box(1);
v___x_2523_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2524_ = l_Lean_instReprKVMap_repr___redArg(v_data_2517_);
v___x_2525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
lean_ctor_set(v___x_2526_, 1, v___x_2522_);
v___x_2527_ = l_Lean_instReprExpr_repr(v_expr_2518_, v___x_2519_);
v___x_2528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2526_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
lean_inc(v___y_2521_);
v___x_2529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___y_2521_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = 0;
v___x_2531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set_uint8(v___x_2531_, sizeof(void*)*1, v___x_2530_);
v___x_2532_ = l_Repr_addAppParen(v___x_2531_, v_prec_2317_);
return v___x_2532_;
}
}
default: 
{
lean_object* v_typeName_2536_; lean_object* v_idx_2537_; lean_object* v_struct_2538_; lean_object* v___x_2539_; lean_object* v___y_2541_; uint8_t v___x_2557_; 
v_typeName_2536_ = lean_ctor_get(v_x_2316_, 0);
lean_inc(v_typeName_2536_);
v_idx_2537_ = lean_ctor_get(v_x_2316_, 1);
lean_inc(v_idx_2537_);
v_struct_2538_ = lean_ctor_get(v_x_2316_, 2);
lean_inc_ref(v_struct_2538_);
lean_dec_ref_known(v_x_2316_, 3);
v___x_2539_ = lean_unsigned_to_nat(1024u);
v___x_2557_ = lean_nat_dec_le(v___x_2539_, v_prec_2317_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2541_ = v___x_2558_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2541_ = v___x_2559_;
goto v___jp_2540_;
}
v___jp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2542_ = lean_box(1);
v___x_2543_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2544_ = l_Lean_Name_reprPrec(v_typeName_2536_, v___x_2539_);
v___x_2545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v___x_2542_);
v___x_2547_ = l_Nat_reprFast(v_idx_2537_);
v___x_2548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
v___x_2549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2546_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___x_2542_);
v___x_2551_ = l_Lean_instReprExpr_repr(v_struct_2538_, v___x_2539_);
v___x_2552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
lean_inc(v___y_2541_);
v___x_2553_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___y_2541_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = 0;
v___x_2555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*1, v___x_2554_);
v___x_2556_ = l_Repr_addAppParen(v___x_2555_, v_prec_2317_);
return v___x_2556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2560_, lean_object* v_prec_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_instReprExpr_repr(v_x_2560_, v_prec_2561_);
lean_dec(v_prec_2561_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2563_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_nat_to_int(v_a_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2565_, lean_object* v_n_2566_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2565_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2568_, lean_object* v_n_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2568_, v_n_2569_);
lean_dec(v_n_2569_);
return v_res_2570_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = lean_box(0);
v___x_2577_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2578_ = l_Lean_Expr_const___override(v___x_2577_, v___x_2576_);
return v___x_2578_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2592_){
_start:
{
switch(lean_obj_tag(v_x_2592_))
{
case 0:
{
lean_object* v___x_2593_; 
v___x_2593_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2593_;
}
case 1:
{
lean_object* v___x_2594_; 
v___x_2594_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2594_;
}
case 2:
{
lean_object* v___x_2595_; 
v___x_2595_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2595_;
}
case 3:
{
lean_object* v___x_2596_; 
v___x_2596_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2596_;
}
case 4:
{
lean_object* v___x_2597_; 
v___x_2597_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2597_;
}
case 5:
{
lean_object* v___x_2598_; 
v___x_2598_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2598_;
}
case 6:
{
lean_object* v___x_2599_; 
v___x_2599_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2599_;
}
case 7:
{
lean_object* v___x_2600_; 
v___x_2600_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2600_;
}
case 8:
{
lean_object* v___x_2601_; 
v___x_2601_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2601_;
}
case 9:
{
lean_object* v___x_2602_; 
v___x_2602_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2602_;
}
case 10:
{
lean_object* v___x_2603_; 
v___x_2603_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2603_;
}
default: 
{
lean_object* v___x_2604_; 
v___x_2604_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Expr_ctorName(v_x_2605_);
lean_dec_ref(v_x_2605_);
return v_res_2606_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2607_){
_start:
{
uint64_t v___x_2608_; uint32_t v___x_2609_; uint64_t v___x_2610_; 
v___x_2608_ = lean_expr_data(v_e_2607_);
v___x_2609_ = lean_uint64_to_uint32(v___x_2608_);
v___x_2610_ = lean_uint32_to_uint64(v___x_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2611_){
_start:
{
uint64_t v_res_2612_; lean_object* v_r_2613_; 
v_res_2612_ = l_Lean_Expr_hash(v_e_2611_);
lean_dec_ref(v_e_2611_);
v_r_2613_ = lean_box_uint64(v_res_2612_);
return v_r_2613_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2616_){
_start:
{
uint64_t v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = lean_expr_data(v_e_2616_);
v___x_2618_ = l_Lean_Expr_Data_hasFVar(v___x_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2619_){
_start:
{
uint8_t v_res_2620_; lean_object* v_r_2621_; 
v_res_2620_ = l_Lean_Expr_hasFVar(v_e_2619_);
lean_dec_ref(v_e_2619_);
v_r_2621_ = lean_box(v_res_2620_);
return v_r_2621_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2622_){
_start:
{
uint64_t v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = lean_expr_data(v_e_2622_);
v___x_2624_ = l_Lean_Expr_Data_hasExprMVar(v___x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2625_){
_start:
{
uint8_t v_res_2626_; lean_object* v_r_2627_; 
v_res_2626_ = l_Lean_Expr_hasExprMVar(v_e_2625_);
lean_dec_ref(v_e_2625_);
v_r_2627_ = lean_box(v_res_2626_);
return v_r_2627_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2628_){
_start:
{
uint64_t v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = lean_expr_data(v_e_2628_);
v___x_2630_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2631_){
_start:
{
uint8_t v_res_2632_; lean_object* v_r_2633_; 
v_res_2632_ = l_Lean_Expr_hasLevelMVar(v_e_2631_);
lean_dec_ref(v_e_2631_);
v_r_2633_ = lean_box(v_res_2632_);
return v_r_2633_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2634_){
_start:
{
uint64_t v_d_2635_; uint8_t v___x_2636_; 
v_d_2635_ = lean_expr_data(v_e_2634_);
v___x_2636_ = l_Lean_Expr_Data_hasExprMVar(v_d_2635_);
if (v___x_2636_ == 0)
{
uint8_t v___x_2637_; 
v___x_2637_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2635_);
return v___x_2637_;
}
else
{
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2638_){
_start:
{
uint8_t v_res_2639_; lean_object* v_r_2640_; 
v_res_2639_ = l_Lean_Expr_hasMVar(v_e_2638_);
lean_dec_ref(v_e_2638_);
v_r_2640_ = lean_box(v_res_2639_);
return v_r_2640_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2641_){
_start:
{
uint64_t v___x_2642_; uint8_t v___x_2643_; 
v___x_2642_ = lean_expr_data(v_e_2641_);
v___x_2643_ = l_Lean_Expr_Data_hasLevelParam(v___x_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2644_){
_start:
{
uint8_t v_res_2645_; lean_object* v_r_2646_; 
v_res_2645_ = l_Lean_Expr_hasLevelParam(v_e_2644_);
lean_dec_ref(v_e_2644_);
v_r_2646_ = lean_box(v_res_2645_);
return v_r_2646_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2647_){
_start:
{
uint64_t v___x_2648_; uint8_t v___x_2649_; uint32_t v___x_2650_; 
v___x_2648_ = lean_expr_data(v_e_2647_);
v___x_2649_ = l_Lean_Expr_Data_approxDepth(v___x_2648_);
v___x_2650_ = lean_uint8_to_uint32(v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2651_){
_start:
{
uint32_t v_res_2652_; lean_object* v_r_2653_; 
v_res_2652_ = l_Lean_Expr_approxDepth(v_e_2651_);
lean_dec_ref(v_e_2651_);
v_r_2653_ = lean_box_uint32(v_res_2652_);
return v_r_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2654_){
_start:
{
uint64_t v___x_2655_; uint32_t v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = lean_expr_data(v_e_2654_);
v___x_2656_ = l_Lean_Expr_Data_looseBVarRange(v___x_2655_);
v___x_2657_ = lean_uint32_to_nat(v___x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_Expr_looseBVarRange(v_e_2658_);
lean_dec_ref(v_e_2658_);
return v_res_2659_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2660_){
_start:
{
switch(lean_obj_tag(v_e_2660_))
{
case 7:
{
uint8_t v_binderInfo_2661_; 
v_binderInfo_2661_ = lean_ctor_get_uint8(v_e_2660_, sizeof(void*)*3 + 8);
return v_binderInfo_2661_;
}
case 6:
{
uint8_t v_binderInfo_2662_; 
v_binderInfo_2662_ = lean_ctor_get_uint8(v_e_2660_, sizeof(void*)*3 + 8);
return v_binderInfo_2662_;
}
default: 
{
uint8_t v___x_2663_; 
v___x_2663_ = 0;
return v___x_2663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2664_){
_start:
{
uint8_t v_res_2665_; lean_object* v_r_2666_; 
v_res_2665_ = l_Lean_Expr_binderInfo(v_e_2664_);
lean_dec_ref(v_e_2664_);
v_r_2666_ = lean_box(v_res_2665_);
return v_r_2666_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2667_){
_start:
{
uint64_t v___x_2668_; 
v___x_2668_ = l_Lean_Expr_hash(v_a_2667_);
lean_dec_ref(v_a_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2669_){
_start:
{
uint64_t v_res_2670_; lean_object* v_r_2671_; 
v_res_2670_ = lean_expr_hash(v_a_2669_);
v_r_2671_ = lean_box_uint64(v_res_2670_);
return v_r_2671_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2672_){
_start:
{
uint8_t v___x_2673_; 
v___x_2673_ = l_Lean_Expr_hasFVar(v_e_2672_);
lean_dec_ref(v_e_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2674_){
_start:
{
uint8_t v_res_2675_; lean_object* v_r_2676_; 
v_res_2675_ = lean_expr_has_fvar(v_e_2674_);
v_r_2676_ = lean_box(v_res_2675_);
return v_r_2676_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2677_){
_start:
{
uint8_t v___x_2678_; 
v___x_2678_ = l_Lean_Expr_hasExprMVar(v_e_2677_);
lean_dec_ref(v_e_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2679_){
_start:
{
uint8_t v_res_2680_; lean_object* v_r_2681_; 
v_res_2680_ = lean_expr_has_expr_mvar(v_e_2679_);
v_r_2681_ = lean_box(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2682_){
_start:
{
uint8_t v___x_2683_; 
v___x_2683_ = l_Lean_Expr_hasLevelMVar(v_e_2682_);
lean_dec_ref(v_e_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2684_){
_start:
{
uint8_t v_res_2685_; lean_object* v_r_2686_; 
v_res_2685_ = lean_expr_has_level_mvar(v_e_2684_);
v_r_2686_ = lean_box(v_res_2685_);
return v_r_2686_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2687_){
_start:
{
uint8_t v___x_2688_; 
v___x_2688_ = l_Lean_Expr_hasLevelParam(v_e_2687_);
lean_dec_ref(v_e_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2689_){
_start:
{
uint8_t v_res_2690_; lean_object* v_r_2691_; 
v_res_2690_ = lean_expr_has_level_param(v_e_2689_);
v_r_2691_ = lean_box(v_res_2690_);
return v_r_2691_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2692_){
_start:
{
uint64_t v___x_2693_; uint32_t v___x_2694_; 
v___x_2693_ = lean_expr_data(v_e_2692_);
lean_dec_ref(v_e_2692_);
v___x_2694_ = l_Lean_Expr_Data_looseBVarRange(v___x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2695_){
_start:
{
uint32_t v_res_2696_; lean_object* v_r_2697_; 
v_res_2696_ = lean_expr_loose_bvar_range(v_e_2695_);
v_r_2697_ = lean_box_uint32(v_res_2696_);
return v_r_2697_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2698_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = l_Lean_Expr_binderInfo(v_e_2698_);
lean_dec_ref(v_e_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2700_){
_start:
{
uint8_t v_res_2701_; lean_object* v_r_2702_; 
v_res_2701_ = lean_expr_binder_info(v_e_2700_);
v_r_2702_ = lean_box(v_res_2701_);
return v_r_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2703_, lean_object* v_us_2704_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_Expr_const___override(v_declName_2703_, v_us_2704_);
return v___x_2705_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_box(0);
v___x_2710_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2711_ = l_Lean_Expr_const___override(v___x_2710_, v___x_2709_);
return v___x_2711_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_box(0);
v___x_2716_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2717_ = l_Lean_Expr_const___override(v___x_2716_, v___x_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2718_){
_start:
{
if (lean_obj_tag(v_x_2718_) == 0)
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2719_;
}
else
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_Literal_type(v_x_2721_);
lean_dec_ref(v_x_2721_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2723_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_Literal_type(v_a_2723_);
lean_dec_ref(v_a_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_Expr_bvar___override(v_idx_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2727_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Expr_sort___override(v_u_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2729_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_Expr_fvar___override(v_fvarId_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2731_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Expr_mvar___override(v_mvarId_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2733_, lean_object* v_e_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_Expr_mdata___override(v_m_2733_, v_e_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2736_, lean_object* v_idx_2737_, lean_object* v_struct_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Expr_proj___override(v_structName_2736_, v_idx_2737_, v_struct_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_Expr_app___override(v_f_2740_, v_a_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2743_, uint8_t v_bi_2744_, lean_object* v_t_2745_, lean_object* v_b_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Expr_lam___override(v_x_2743_, v_t_2745_, v_b_2746_, v_bi_2744_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2748_, lean_object* v_bi_2749_, lean_object* v_t_2750_, lean_object* v_b_2751_){
_start:
{
uint8_t v_bi_boxed_2752_; lean_object* v_res_2753_; 
v_bi_boxed_2752_ = lean_unbox(v_bi_2749_);
v_res_2753_ = l_Lean_mkLambda(v_x_2748_, v_bi_boxed_2752_, v_t_2750_, v_b_2751_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2754_, uint8_t v_bi_2755_, lean_object* v_t_2756_, lean_object* v_b_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_Expr_forallE___override(v_x_2754_, v_t_2756_, v_b_2757_, v_bi_2755_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2759_, lean_object* v_bi_2760_, lean_object* v_t_2761_, lean_object* v_b_2762_){
_start:
{
uint8_t v_bi_boxed_2763_; lean_object* v_res_2764_; 
v_bi_boxed_2763_ = lean_unbox(v_bi_2760_);
v_res_2764_ = l_Lean_mkForall(v_x_2759_, v_bi_boxed_2763_, v_t_2761_, v_b_2762_);
return v_res_2764_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = lean_box(0);
v___x_2772_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2773_ = l_Lean_Expr_const___override(v___x_2772_, v___x_2771_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2774_){
_start:
{
lean_object* v___x_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2775_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2776_ = 0;
v___x_2777_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2778_ = l_Lean_Expr_forallE___override(v___x_2775_, v___x_2777_, v_type_2774_, v___x_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2779_){
_start:
{
lean_object* v___x_2780_; uint8_t v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2780_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2781_ = 0;
v___x_2782_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2783_ = l_Lean_Expr_lam___override(v___x_2780_, v___x_2782_, v_type_2779_, v___x_2781_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2784_, lean_object* v_t_2785_, lean_object* v_v_2786_, lean_object* v_b_2787_, uint8_t v_nondep_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_Expr_letE___override(v_x_2784_, v_t_2785_, v_v_2786_, v_b_2787_, v_nondep_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2790_, lean_object* v_t_2791_, lean_object* v_v_2792_, lean_object* v_b_2793_, lean_object* v_nondep_2794_){
_start:
{
uint8_t v_nondep_boxed_2795_; lean_object* v_res_2796_; 
v_nondep_boxed_2795_ = lean_unbox(v_nondep_2794_);
v_res_2796_ = l_Lean_mkLet(v_x_2790_, v_t_2791_, v_v_2792_, v_b_2793_, v_nondep_boxed_2795_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2797_, lean_object* v_t_2798_, lean_object* v_v_2799_, lean_object* v_b_2800_){
_start:
{
uint8_t v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = 1;
v___x_2802_ = l_Lean_Expr_letE___override(v_x_2797_, v_t_2798_, v_v_2799_, v_b_2800_, v___x_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2803_, lean_object* v_a_2804_, lean_object* v_b_2805_){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = l_Lean_Expr_app___override(v_f_2803_, v_a_2804_);
v___x_2807_ = l_Lean_Expr_app___override(v___x_2806_, v_b_2805_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2808_, lean_object* v_a_2809_, lean_object* v_b_2810_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_mkAppB(v_f_2808_, v_a_2809_, v_b_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2812_, lean_object* v_a_2813_, lean_object* v_b_2814_, lean_object* v_c_2815_){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = l_Lean_mkAppB(v_f_2812_, v_a_2813_, v_b_2814_);
v___x_2817_ = l_Lean_Expr_app___override(v___x_2816_, v_c_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2818_, lean_object* v_a_2819_, lean_object* v_b_2820_, lean_object* v_c_2821_, lean_object* v_d_2822_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = l_Lean_mkAppB(v_f_2818_, v_a_2819_, v_b_2820_);
v___x_2824_ = l_Lean_mkAppB(v___x_2823_, v_c_2821_, v_d_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2825_, lean_object* v_a_2826_, lean_object* v_b_2827_, lean_object* v_c_2828_, lean_object* v_d_2829_, lean_object* v_e_2830_){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = l_Lean_mkApp4(v_f_2825_, v_a_2826_, v_b_2827_, v_c_2828_, v_d_2829_);
v___x_2832_ = l_Lean_Expr_app___override(v___x_2831_, v_e_2830_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2833_, lean_object* v_a_2834_, lean_object* v_b_2835_, lean_object* v_c_2836_, lean_object* v_d_2837_, lean_object* v_e_u2081_2838_, lean_object* v_e_u2082_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = l_Lean_mkApp4(v_f_2833_, v_a_2834_, v_b_2835_, v_c_2836_, v_d_2837_);
v___x_2841_ = l_Lean_mkAppB(v___x_2840_, v_e_u2081_2838_, v_e_u2082_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2842_, lean_object* v_a_2843_, lean_object* v_b_2844_, lean_object* v_c_2845_, lean_object* v_d_2846_, lean_object* v_e_u2081_2847_, lean_object* v_e_u2082_2848_, lean_object* v_e_u2083_2849_){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = l_Lean_mkApp4(v_f_2842_, v_a_2843_, v_b_2844_, v_c_2845_, v_d_2846_);
v___x_2851_ = l_Lean_mkApp3(v___x_2850_, v_e_u2081_2847_, v_e_u2082_2848_, v_e_u2083_2849_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2852_, lean_object* v_a_2853_, lean_object* v_b_2854_, lean_object* v_c_2855_, lean_object* v_d_2856_, lean_object* v_e_u2081_2857_, lean_object* v_e_u2082_2858_, lean_object* v_e_u2083_2859_, lean_object* v_e_u2084_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = l_Lean_mkApp4(v_f_2852_, v_a_2853_, v_b_2854_, v_c_2855_, v_d_2856_);
v___x_2862_ = l_Lean_mkApp4(v___x_2861_, v_e_u2081_2857_, v_e_u2082_2858_, v_e_u2083_2859_, v_e_u2084_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2863_, lean_object* v_a_2864_, lean_object* v_b_2865_, lean_object* v_c_2866_, lean_object* v_d_2867_, lean_object* v_e_u2081_2868_, lean_object* v_e_u2082_2869_, lean_object* v_e_u2083_2870_, lean_object* v_e_u2084_2871_, lean_object* v_e_u2085_2872_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = l_Lean_mkApp4(v_f_2863_, v_a_2864_, v_b_2865_, v_c_2866_, v_d_2867_);
v___x_2874_ = l_Lean_mkApp5(v___x_2873_, v_e_u2081_2868_, v_e_u2082_2869_, v_e_u2083_2870_, v_e_u2084_2871_, v_e_u2085_2872_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2875_, lean_object* v_a_2876_, lean_object* v_b_2877_, lean_object* v_c_2878_, lean_object* v_d_2879_, lean_object* v_e_u2081_2880_, lean_object* v_e_u2082_2881_, lean_object* v_e_u2083_2882_, lean_object* v_e_u2084_2883_, lean_object* v_e_u2085_2884_, lean_object* v_e_u2086_2885_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = l_Lean_mkApp4(v_f_2875_, v_a_2876_, v_b_2877_, v_c_2878_, v_d_2879_);
v___x_2887_ = l_Lean_mkApp6(v___x_2886_, v_e_u2081_2880_, v_e_u2082_2881_, v_e_u2083_2882_, v_e_u2084_2883_, v_e_u2085_2884_, v_e_u2086_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Expr_lit___override(v_l_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2890_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v_n_2890_);
v___x_2892_ = l_Lean_Expr_lit___override(v___x_2891_);
return v___x_2892_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = lean_box(0);
v___x_2897_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2898_ = l_Lean_Expr_const___override(v___x_2897_, v___x_2896_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2899_){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2901_ = l_Lean_Expr_app___override(v___x_2900_, v_n_2899_);
return v___x_2901_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2911_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2912_ = l_Lean_Expr_const___override(v___x_2911_, v___x_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2913_){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2914_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2915_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2913_);
v___x_2916_ = l_Lean_mkInstOfNatNat(v_n_2913_);
v___x_2917_ = l_Lean_mkApp3(v___x_2914_, v___x_2915_, v_n_2913_, v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2918_){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = l_Lean_mkRawNatLit(v_n_2918_);
v___x_2920_ = l_Lean_mkNatLitCore(v___x_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2921_){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2922_, 0, v_s_2921_);
v___x_2923_ = l_Lean_Expr_lit___override(v___x_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_Expr_bvar___override(v_idx_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2926_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_Expr_fvar___override(v_fvarId_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_Expr_sort___override(v_u_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2930_, lean_object* v_lvls_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Expr_const___override(v_c_2930_, v_lvls_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_Expr_app___override(v_f_2933_, v_a_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2936_, lean_object* v_d_2937_, lean_object* v_b_2938_, uint8_t v_bi_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_Expr_lam___override(v_n_2936_, v_d_2937_, v_b_2938_, v_bi_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2941_, lean_object* v_d_2942_, lean_object* v_b_2943_, lean_object* v_bi_2944_){
_start:
{
uint8_t v_bi_boxed_2945_; lean_object* v_res_2946_; 
v_bi_boxed_2945_ = lean_unbox(v_bi_2944_);
v_res_2946_ = lean_expr_mk_lambda(v_n_2941_, v_d_2942_, v_b_2943_, v_bi_boxed_2945_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2947_, lean_object* v_d_2948_, lean_object* v_b_2949_, uint8_t v_bi_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Lean_Expr_forallE___override(v_n_2947_, v_d_2948_, v_b_2949_, v_bi_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2952_, lean_object* v_d_2953_, lean_object* v_b_2954_, lean_object* v_bi_2955_){
_start:
{
uint8_t v_bi_boxed_2956_; lean_object* v_res_2957_; 
v_bi_boxed_2956_ = lean_unbox(v_bi_2955_);
v_res_2957_ = lean_expr_mk_forall(v_n_2952_, v_d_2953_, v_b_2954_, v_bi_boxed_2956_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2958_, lean_object* v_t_2959_, lean_object* v_v_2960_, lean_object* v_b_2961_, uint8_t v_nondep_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Expr_letE___override(v_n_2958_, v_t_2959_, v_v_2960_, v_b_2961_, v_nondep_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2964_, lean_object* v_t_2965_, lean_object* v_v_2966_, lean_object* v_b_2967_, lean_object* v_nondep_2968_){
_start:
{
uint8_t v_nondep_boxed_2969_; lean_object* v_res_2970_; 
v_nondep_boxed_2969_ = lean_unbox(v_nondep_2968_);
v_res_2970_ = lean_expr_mk_let(v_n_2964_, v_t_2965_, v_v_2966_, v_b_2967_, v_nondep_boxed_2969_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Expr_lit___override(v_l_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_2973_, lean_object* v_e_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Expr_mdata___override(v_m_2973_, v_e_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_2976_, lean_object* v_idx_2977_, lean_object* v_struct_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Expr_proj___override(v_structName_2976_, v_idx_2977_, v_struct_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_2980_, size_t v_i_2981_, size_t v_stop_2982_, lean_object* v_b_2983_){
_start:
{
uint8_t v___x_2984_; 
v___x_2984_ = lean_usize_dec_eq(v_i_2981_, v_stop_2982_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; size_t v___x_2987_; size_t v___x_2988_; 
v___x_2985_ = lean_array_uget_borrowed(v_as_2980_, v_i_2981_);
lean_inc(v___x_2985_);
v___x_2986_ = l_Lean_Expr_app___override(v_b_2983_, v___x_2985_);
v___x_2987_ = ((size_t)1ULL);
v___x_2988_ = lean_usize_add(v_i_2981_, v___x_2987_);
v_i_2981_ = v___x_2988_;
v_b_2983_ = v___x_2986_;
goto _start;
}
else
{
return v_b_2983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_2990_, lean_object* v_i_2991_, lean_object* v_stop_2992_, lean_object* v_b_2993_){
_start:
{
size_t v_i_boxed_2994_; size_t v_stop_boxed_2995_; lean_object* v_res_2996_; 
v_i_boxed_2994_ = lean_unbox_usize(v_i_2991_);
lean_dec(v_i_2991_);
v_stop_boxed_2995_ = lean_unbox_usize(v_stop_2992_);
lean_dec(v_stop_2992_);
v_res_2996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_2990_, v_i_boxed_2994_, v_stop_boxed_2995_, v_b_2993_);
lean_dec_ref(v_as_2990_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_2997_, lean_object* v_args_2998_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_2999_ = lean_unsigned_to_nat(0u);
v___x_3000_ = lean_array_get_size(v_args_2998_);
v___x_3001_ = lean_nat_dec_lt(v___x_2999_, v___x_3000_);
if (v___x_3001_ == 0)
{
return v_f_2997_;
}
else
{
size_t v___x_3002_; size_t v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = ((size_t)0ULL);
v___x_3003_ = lean_usize_of_nat(v___x_3000_);
v___x_3004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_2998_, v___x_3002_, v___x_3003_, v_f_2997_);
return v___x_3004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3005_, lean_object* v_args_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_mkAppN(v_f_3005_, v_args_3006_);
lean_dec_ref(v_args_3006_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3008_, lean_object* v_args_3009_, lean_object* v_i_3010_, lean_object* v_e_3011_){
_start:
{
uint8_t v___x_3012_; 
v___x_3012_ = lean_nat_dec_lt(v_i_3010_, v_n_3008_);
if (v___x_3012_ == 0)
{
lean_dec(v_i_3010_);
return v_e_3011_;
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3013_ = l_Lean_instInhabitedExpr;
v___x_3014_ = lean_unsigned_to_nat(1u);
v___x_3015_ = lean_nat_add(v_i_3010_, v___x_3014_);
v___x_3016_ = lean_array_get_borrowed(v___x_3013_, v_args_3009_, v_i_3010_);
lean_dec(v_i_3010_);
lean_inc(v___x_3016_);
v___x_3017_ = l_Lean_Expr_app___override(v_e_3011_, v___x_3016_);
v_i_3010_ = v___x_3015_;
v_e_3011_ = v___x_3017_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3019_, lean_object* v_args_3020_, lean_object* v_i_3021_, lean_object* v_e_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3019_, v_args_3020_, v_i_3021_, v_e_3022_);
lean_dec_ref(v_args_3020_);
lean_dec(v_n_3019_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3024_, lean_object* v_i_3025_, lean_object* v_j_3026_, lean_object* v_args_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3026_, v_args_3027_, v_i_3025_, v_f_3024_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3029_, lean_object* v_i_3030_, lean_object* v_j_3031_, lean_object* v_args_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_mkAppRange(v_f_3029_, v_i_3030_, v_j_3031_, v_args_3032_);
lean_dec_ref(v_args_3032_);
lean_dec(v_j_3031_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3034_, size_t v_i_3035_, size_t v_stop_3036_, lean_object* v_b_3037_){
_start:
{
uint8_t v___x_3038_; 
v___x_3038_ = lean_usize_dec_eq(v_i_3035_, v_stop_3036_);
if (v___x_3038_ == 0)
{
size_t v___x_3039_; size_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3039_ = ((size_t)1ULL);
v___x_3040_ = lean_usize_sub(v_i_3035_, v___x_3039_);
v___x_3041_ = lean_array_uget_borrowed(v_as_3034_, v___x_3040_);
lean_inc(v___x_3041_);
v___x_3042_ = l_Lean_Expr_app___override(v_b_3037_, v___x_3041_);
v_i_3035_ = v___x_3040_;
v_b_3037_ = v___x_3042_;
goto _start;
}
else
{
return v_b_3037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3044_, lean_object* v_i_3045_, lean_object* v_stop_3046_, lean_object* v_b_3047_){
_start:
{
size_t v_i_boxed_3048_; size_t v_stop_boxed_3049_; lean_object* v_res_3050_; 
v_i_boxed_3048_ = lean_unbox_usize(v_i_3045_);
lean_dec(v_i_3045_);
v_stop_boxed_3049_ = lean_unbox_usize(v_stop_3046_);
lean_dec(v_stop_3046_);
v_res_3050_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3044_, v_i_boxed_3048_, v_stop_boxed_3049_, v_b_3047_);
lean_dec_ref(v_as_3044_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3051_, lean_object* v_revArgs_3052_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3053_ = lean_array_get_size(v_revArgs_3052_);
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = lean_nat_dec_lt(v___x_3054_, v___x_3053_);
if (v___x_3055_ == 0)
{
return v_fn_3051_;
}
else
{
size_t v___x_3056_; size_t v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = lean_usize_of_nat(v___x_3053_);
v___x_3057_ = ((size_t)0ULL);
v___x_3058_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3052_, v___x_3056_, v___x_3057_, v_fn_3051_);
return v___x_3058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3059_, lean_object* v_revArgs_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_mkAppRev(v_fn_3059_, v_revArgs_3060_);
lean_dec_ref(v_revArgs_3060_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = lean_expr_dbg_to_string(v_e_3063_);
lean_dec_ref(v_e_3063_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3067_, lean_object* v_b_3068_){
_start:
{
uint8_t v_res_3069_; lean_object* v_r_3070_; 
v_res_3069_ = lean_expr_quick_lt(v_a_3067_, v_b_3068_);
lean_dec_ref(v_b_3068_);
lean_dec_ref(v_a_3067_);
v_r_3070_ = lean_box(v_res_3069_);
return v_r_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3073_, lean_object* v_b_3074_){
_start:
{
uint8_t v_res_3075_; lean_object* v_r_3076_; 
v_res_3075_ = lean_expr_lt(v_a_3073_, v_b_3074_);
lean_dec_ref(v_b_3074_);
lean_dec_ref(v_a_3073_);
v_r_3076_ = lean_box(v_res_3075_);
return v_r_3076_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3077_, lean_object* v_b_3078_){
_start:
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_expr_quick_lt(v_a_3077_, v_b_3078_);
if (v___x_3079_ == 0)
{
uint8_t v___x_3080_; 
v___x_3080_ = lean_expr_quick_lt(v_b_3078_, v_a_3077_);
if (v___x_3080_ == 0)
{
uint8_t v___x_3081_; 
v___x_3081_ = 1;
return v___x_3081_;
}
else
{
uint8_t v___x_3082_; 
v___x_3082_ = 2;
return v___x_3082_;
}
}
else
{
uint8_t v___x_3083_; 
v___x_3083_ = 0;
return v___x_3083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3084_, lean_object* v_b_3085_){
_start:
{
uint8_t v_res_3086_; lean_object* v_r_3087_; 
v_res_3086_ = l_Lean_Expr_quickComp(v_a_3084_, v_b_3085_);
lean_dec_ref(v_b_3085_);
lean_dec_ref(v_a_3084_);
v_r_3087_ = lean_box(v_res_3086_);
return v_r_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3090_, lean_object* v_b_3091_){
_start:
{
uint8_t v_res_3092_; lean_object* v_r_3093_; 
v_res_3092_ = lean_expr_eqv(v_a_3090_, v_b_3091_);
lean_dec_ref(v_b_3091_);
lean_dec_ref(v_a_3090_);
v_r_3093_ = lean_box(v_res_3092_);
return v_r_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3098_, lean_object* v_b_3099_){
_start:
{
uint8_t v_res_3100_; lean_object* v_r_3101_; 
v_res_3100_ = lean_expr_equal(v_a_3098_, v_b_3099_);
lean_dec_ref(v_b_3099_);
lean_dec_ref(v_a_3098_);
v_r_3101_ = lean_box(v_res_3100_);
return v_r_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqvBudgeted___boxed(lean_object* v_a_3106_, lean_object* v_b_3107_, lean_object* v_budget_3108_, lean_object* v_a_00___x40___internal___hyg_3109_){
_start:
{
size_t v_budget_boxed_3110_; uint8_t v_res_3111_; lean_object* v_r_3112_; 
v_budget_boxed_3110_ = lean_unbox_usize(v_budget_3108_);
lean_dec(v_budget_3108_);
v_res_3111_ = lean_expr_eqv_budgeted(v_a_3106_, v_b_3107_, v_budget_boxed_3110_);
lean_dec_ref(v_b_3107_);
lean_dec_ref(v_a_3106_);
v_r_3112_ = lean_box(v_res_3111_);
return v_r_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equalBudgeted___boxed(lean_object* v_a_3117_, lean_object* v_b_3118_, lean_object* v_budget_3119_, lean_object* v_a_00___x40___internal___hyg_3120_){
_start:
{
size_t v_budget_boxed_3121_; uint8_t v_res_3122_; lean_object* v_r_3123_; 
v_budget_boxed_3121_ = lean_unbox_usize(v_budget_3119_);
lean_dec(v_budget_3119_);
v_res_3122_ = lean_expr_equal_budgeted(v_a_3117_, v_b_3118_, v_budget_boxed_3121_);
lean_dec_ref(v_b_3118_);
lean_dec_ref(v_a_3117_);
v_r_3123_ = lean_box(v_res_3122_);
return v_r_3123_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3124_){
_start:
{
if (lean_obj_tag(v_x_3124_) == 3)
{
uint8_t v___x_3125_; 
v___x_3125_ = 1;
return v___x_3125_;
}
else
{
uint8_t v___x_3126_; 
v___x_3126_ = 0;
return v___x_3126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3127_){
_start:
{
uint8_t v_res_3128_; lean_object* v_r_3129_; 
v_res_3128_ = l_Lean_Expr_isSort(v_x_3127_);
lean_dec_ref(v_x_3127_);
v_r_3129_ = lean_box(v_res_3128_);
return v_r_3129_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3130_){
_start:
{
if (lean_obj_tag(v_x_3130_) == 3)
{
lean_object* v_u_3131_; 
v_u_3131_ = lean_ctor_get(v_x_3130_, 0);
if (lean_obj_tag(v_u_3131_) == 1)
{
uint8_t v___x_3132_; 
v___x_3132_ = 1;
return v___x_3132_;
}
else
{
uint8_t v___x_3133_; 
v___x_3133_ = 0;
return v___x_3133_;
}
}
else
{
uint8_t v___x_3134_; 
v___x_3134_ = 0;
return v___x_3134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3135_){
_start:
{
uint8_t v_res_3136_; lean_object* v_r_3137_; 
v_res_3136_ = l_Lean_Expr_isType(v_x_3135_);
lean_dec_ref(v_x_3135_);
v_r_3137_ = lean_box(v_res_3136_);
return v_r_3137_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3138_){
_start:
{
if (lean_obj_tag(v_x_3138_) == 3)
{
lean_object* v_u_3139_; 
v_u_3139_ = lean_ctor_get(v_x_3138_, 0);
if (lean_obj_tag(v_u_3139_) == 1)
{
lean_object* v_a_3140_; 
v_a_3140_ = lean_ctor_get(v_u_3139_, 0);
if (lean_obj_tag(v_a_3140_) == 0)
{
uint8_t v___x_3141_; 
v___x_3141_ = 1;
return v___x_3141_;
}
else
{
uint8_t v___x_3142_; 
v___x_3142_ = 0;
return v___x_3142_;
}
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
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3145_){
_start:
{
uint8_t v_res_3146_; lean_object* v_r_3147_; 
v_res_3146_ = l_Lean_Expr_isType0(v_x_3145_);
lean_dec_ref(v_x_3145_);
v_r_3147_ = lean_box(v_res_3146_);
return v_r_3147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3148_){
_start:
{
if (lean_obj_tag(v_x_3148_) == 3)
{
lean_object* v_u_3149_; 
v_u_3149_ = lean_ctor_get(v_x_3148_, 0);
if (lean_obj_tag(v_u_3149_) == 0)
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
else
{
uint8_t v___x_3152_; 
v___x_3152_ = 0;
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3153_){
_start:
{
uint8_t v_res_3154_; lean_object* v_r_3155_; 
v_res_3154_ = l_Lean_Expr_isProp(v_x_3153_);
lean_dec_ref(v_x_3153_);
v_r_3155_ = lean_box(v_res_3154_);
return v_r_3155_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3156_){
_start:
{
if (lean_obj_tag(v_x_3156_) == 0)
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3159_){
_start:
{
uint8_t v_res_3160_; lean_object* v_r_3161_; 
v_res_3160_ = l_Lean_Expr_isBVar(v_x_3159_);
lean_dec_ref(v_x_3159_);
v_r_3161_ = lean_box(v_res_3160_);
return v_r_3161_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3162_){
_start:
{
if (lean_obj_tag(v_x_3162_) == 2)
{
uint8_t v___x_3163_; 
v___x_3163_ = 1;
return v___x_3163_;
}
else
{
uint8_t v___x_3164_; 
v___x_3164_ = 0;
return v___x_3164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3165_){
_start:
{
uint8_t v_res_3166_; lean_object* v_r_3167_; 
v_res_3166_ = l_Lean_Expr_isMVar(v_x_3165_);
lean_dec_ref(v_x_3165_);
v_r_3167_ = lean_box(v_res_3166_);
return v_r_3167_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3168_){
_start:
{
if (lean_obj_tag(v_x_3168_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3171_){
_start:
{
uint8_t v_res_3172_; lean_object* v_r_3173_; 
v_res_3172_ = l_Lean_Expr_isFVar(v_x_3171_);
lean_dec_ref(v_x_3171_);
v_r_3173_ = lean_box(v_res_3172_);
return v_r_3173_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3174_){
_start:
{
if (lean_obj_tag(v_x_3174_) == 5)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3177_){
_start:
{
uint8_t v_res_3178_; lean_object* v_r_3179_; 
v_res_3178_ = l_Lean_Expr_isApp(v_x_3177_);
lean_dec_ref(v_x_3177_);
v_r_3179_ = lean_box(v_res_3178_);
return v_r_3179_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3180_){
_start:
{
if (lean_obj_tag(v_x_3180_) == 11)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3183_){
_start:
{
uint8_t v_res_3184_; lean_object* v_r_3185_; 
v_res_3184_ = l_Lean_Expr_isProj(v_x_3183_);
lean_dec_ref(v_x_3183_);
v_r_3185_ = lean_box(v_res_3184_);
return v_r_3185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3186_){
_start:
{
if (lean_obj_tag(v_x_3186_) == 4)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3189_){
_start:
{
uint8_t v_res_3190_; lean_object* v_r_3191_; 
v_res_3190_ = l_Lean_Expr_isConst(v_x_3189_);
lean_dec_ref(v_x_3189_);
v_r_3191_ = lean_box(v_res_3190_);
return v_r_3191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3192_, lean_object* v_x_3193_){
_start:
{
if (lean_obj_tag(v_x_3192_) == 4)
{
lean_object* v_declName_3194_; uint8_t v___x_3195_; 
v_declName_3194_ = lean_ctor_get(v_x_3192_, 0);
v___x_3195_ = lean_name_eq(v_declName_3194_, v_x_3193_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3197_, lean_object* v_x_3198_){
_start:
{
uint8_t v_res_3199_; lean_object* v_r_3200_; 
v_res_3199_ = l_Lean_Expr_isConstOf(v_x_3197_, v_x_3198_);
lean_dec(v_x_3198_);
lean_dec_ref(v_x_3197_);
v_r_3200_ = lean_box(v_res_3199_);
return v_r_3200_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3201_, lean_object* v_x_3202_){
_start:
{
if (lean_obj_tag(v_x_3201_) == 1)
{
lean_object* v_fvarId_3203_; uint8_t v___x_3204_; 
v_fvarId_3203_ = lean_ctor_get(v_x_3201_, 0);
v___x_3204_ = lean_name_eq(v_fvarId_3203_, v_x_3202_);
return v___x_3204_;
}
else
{
uint8_t v___x_3205_; 
v___x_3205_ = 0;
return v___x_3205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3206_, lean_object* v_x_3207_){
_start:
{
uint8_t v_res_3208_; lean_object* v_r_3209_; 
v_res_3208_ = l_Lean_Expr_isFVarOf(v_x_3206_, v_x_3207_);
lean_dec(v_x_3207_);
lean_dec_ref(v_x_3206_);
v_r_3209_ = lean_box(v_res_3208_);
return v_r_3209_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3210_){
_start:
{
if (lean_obj_tag(v_x_3210_) == 7)
{
uint8_t v___x_3211_; 
v___x_3211_ = 1;
return v___x_3211_;
}
else
{
uint8_t v___x_3212_; 
v___x_3212_ = 0;
return v___x_3212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3213_){
_start:
{
uint8_t v_res_3214_; lean_object* v_r_3215_; 
v_res_3214_ = l_Lean_Expr_isForall(v_x_3213_);
lean_dec_ref(v_x_3213_);
v_r_3215_ = lean_box(v_res_3214_);
return v_r_3215_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3216_){
_start:
{
if (lean_obj_tag(v_x_3216_) == 6)
{
uint8_t v___x_3217_; 
v___x_3217_ = 1;
return v___x_3217_;
}
else
{
uint8_t v___x_3218_; 
v___x_3218_ = 0;
return v___x_3218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3219_){
_start:
{
uint8_t v_res_3220_; lean_object* v_r_3221_; 
v_res_3220_ = l_Lean_Expr_isLambda(v_x_3219_);
lean_dec_ref(v_x_3219_);
v_r_3221_ = lean_box(v_res_3220_);
return v_r_3221_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3222_){
_start:
{
switch(lean_obj_tag(v_x_3222_))
{
case 6:
{
uint8_t v___x_3223_; 
v___x_3223_ = 1;
return v___x_3223_;
}
case 7:
{
uint8_t v___x_3224_; 
v___x_3224_ = 1;
return v___x_3224_;
}
default: 
{
uint8_t v___x_3225_; 
v___x_3225_ = 0;
return v___x_3225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3226_){
_start:
{
uint8_t v_res_3227_; lean_object* v_r_3228_; 
v_res_3227_ = l_Lean_Expr_isBinding(v_x_3226_);
lean_dec_ref(v_x_3226_);
v_r_3228_ = lean_box(v_res_3227_);
return v_r_3228_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3229_){
_start:
{
if (lean_obj_tag(v_x_3229_) == 8)
{
uint8_t v___x_3230_; 
v___x_3230_ = 1;
return v___x_3230_;
}
else
{
uint8_t v___x_3231_; 
v___x_3231_ = 0;
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3232_){
_start:
{
uint8_t v_res_3233_; lean_object* v_r_3234_; 
v_res_3233_ = l_Lean_Expr_isLet(v_x_3232_);
lean_dec_ref(v_x_3232_);
v_r_3234_ = lean_box(v_res_3233_);
return v_r_3234_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3235_){
_start:
{
if (lean_obj_tag(v_x_3235_) == 8)
{
uint8_t v_nondep_3236_; 
v_nondep_3236_ = lean_ctor_get_uint8(v_x_3235_, sizeof(void*)*4 + 8);
return v_nondep_3236_;
}
else
{
uint8_t v___x_3237_; 
v___x_3237_ = 0;
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3238_){
_start:
{
uint8_t v_res_3239_; lean_object* v_r_3240_; 
v_res_3239_ = l_Lean_Expr_isHave(v_x_3238_);
lean_dec_ref(v_x_3238_);
v_r_3240_ = lean_box(v_res_3239_);
return v_r_3240_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3241_){
_start:
{
uint8_t v___x_3242_; 
v___x_3242_ = l_Lean_Expr_isHave(v_a_3241_);
lean_dec_ref(v_a_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3243_){
_start:
{
uint8_t v_res_3244_; lean_object* v_r_3245_; 
v_res_3244_ = lean_expr_is_have(v_a_3243_);
v_r_3245_ = lean_box(v_res_3244_);
return v_r_3245_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3246_){
_start:
{
if (lean_obj_tag(v_x_3246_) == 10)
{
uint8_t v___x_3247_; 
v___x_3247_ = 1;
return v___x_3247_;
}
else
{
uint8_t v___x_3248_; 
v___x_3248_ = 0;
return v___x_3248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3249_){
_start:
{
uint8_t v_res_3250_; lean_object* v_r_3251_; 
v_res_3250_ = l_Lean_Expr_isMData(v_x_3249_);
lean_dec_ref(v_x_3249_);
v_r_3251_ = lean_box(v_res_3250_);
return v_r_3251_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3252_){
_start:
{
if (lean_obj_tag(v_x_3252_) == 9)
{
uint8_t v___x_3253_; 
v___x_3253_ = 1;
return v___x_3253_;
}
else
{
uint8_t v___x_3254_; 
v___x_3254_ = 0;
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3255_){
_start:
{
uint8_t v_res_3256_; lean_object* v_r_3257_; 
v_res_3256_ = l_Lean_Expr_isLit(v_x_3255_);
lean_dec_ref(v_x_3255_);
v_r_3257_ = lean_box(v_res_3256_);
return v_r_3257_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3258_){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = l_Lean_instInhabitedExpr;
v___x_3260_ = lean_panic_fn_borrowed(v___x_3259_, v_msg_3258_);
return v___x_3260_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3264_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3265_ = lean_unsigned_to_nat(15u);
v___x_3266_ = lean_unsigned_to_nat(967u);
v___x_3267_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3268_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3269_ = l_mkPanicMessageWithDecl(v___x_3268_, v___x_3267_, v___x_3266_, v___x_3265_, v___x_3264_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3270_){
_start:
{
if (lean_obj_tag(v_x_3270_) == 5)
{
lean_object* v_fn_3271_; 
v_fn_3271_ = lean_ctor_get(v_x_3270_, 0);
lean_inc_ref(v_fn_3271_);
return v_fn_3271_;
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3273_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3272_);
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_Expr_appFn_x21(v_x_3274_);
lean_dec_ref(v_x_3274_);
return v_res_3275_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3277_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3278_ = lean_unsigned_to_nat(15u);
v___x_3279_ = lean_unsigned_to_nat(971u);
v___x_3280_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3281_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3282_ = l_mkPanicMessageWithDecl(v___x_3281_, v___x_3280_, v___x_3279_, v___x_3278_, v___x_3277_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3283_){
_start:
{
if (lean_obj_tag(v_x_3283_) == 5)
{
lean_object* v_arg_3284_; 
v_arg_3284_ = lean_ctor_get(v_x_3283_, 1);
lean_inc_ref(v_arg_3284_);
return v_arg_3284_;
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3286_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3285_);
return v___x_3286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_Expr_appArg_x21(v_x_3287_);
lean_dec_ref(v_x_3287_);
return v_res_3288_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3290_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3291_ = lean_unsigned_to_nat(17u);
v___x_3292_ = lean_unsigned_to_nat(976u);
v___x_3293_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3294_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3295_ = l_mkPanicMessageWithDecl(v___x_3294_, v___x_3293_, v___x_3292_, v___x_3291_, v___x_3290_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3296_){
_start:
{
switch(lean_obj_tag(v_x_3296_))
{
case 10:
{
lean_object* v_expr_3297_; 
v_expr_3297_ = lean_ctor_get(v_x_3296_, 1);
v_x_3296_ = v_expr_3297_;
goto _start;
}
case 5:
{
lean_object* v_fn_3299_; 
v_fn_3299_ = lean_ctor_get(v_x_3296_, 0);
lean_inc_ref(v_fn_3299_);
return v_fn_3299_;
}
default: 
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3301_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3300_);
return v___x_3301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_Expr_appFn_x21_x27(v_x_3302_);
lean_dec_ref(v_x_3302_);
return v_res_3303_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3305_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3306_ = lean_unsigned_to_nat(17u);
v___x_3307_ = lean_unsigned_to_nat(981u);
v___x_3308_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3309_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3310_ = l_mkPanicMessageWithDecl(v___x_3309_, v___x_3308_, v___x_3307_, v___x_3306_, v___x_3305_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3311_){
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
lean_object* v_arg_3314_; 
v_arg_3314_ = lean_ctor_get(v_x_3311_, 1);
lean_inc_ref(v_arg_3314_);
return v_arg_3314_;
}
default: 
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3316_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3315_);
return v___x_3316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_Expr_appArg_x21_x27(v_x_3317_);
lean_dec_ref(v_x_3317_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3319_){
_start:
{
lean_object* v_arg_3320_; 
v_arg_3320_ = lean_ctor_get(v_e_3319_, 1);
lean_inc_ref(v_arg_3320_);
return v_arg_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Expr_appArg___redArg(v_e_3321_);
lean_dec_ref(v_e_3321_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3323_, lean_object* v_h_3324_){
_start:
{
lean_object* v_arg_3325_; 
v_arg_3325_ = lean_ctor_get(v_e_3323_, 1);
lean_inc_ref(v_arg_3325_);
return v_arg_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3326_, lean_object* v_h_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_Expr_appArg(v_e_3326_, v_h_3327_);
lean_dec_ref(v_e_3326_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3329_){
_start:
{
lean_object* v_fn_3330_; 
v_fn_3330_ = lean_ctor_get(v_e_3329_, 0);
lean_inc_ref(v_fn_3330_);
return v_fn_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_Expr_appFn___redArg(v_e_3331_);
lean_dec_ref(v_e_3331_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3333_, lean_object* v_h_3334_){
_start:
{
lean_object* v_fn_3335_; 
v_fn_3335_ = lean_ctor_get(v_e_3333_, 0);
lean_inc_ref(v_fn_3335_);
return v_fn_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3336_, lean_object* v_h_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_Expr_appFn(v_e_3336_, v_h_3337_);
lean_dec_ref(v_e_3336_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3339_){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_panic_fn_borrowed(v___x_3340_, v_msg_3339_);
return v___x_3341_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3344_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3345_ = lean_unsigned_to_nat(14u);
v___x_3346_ = lean_unsigned_to_nat(993u);
v___x_3347_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3348_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3349_ = l_mkPanicMessageWithDecl(v___x_3348_, v___x_3347_, v___x_3346_, v___x_3345_, v___x_3344_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3350_){
_start:
{
if (lean_obj_tag(v_x_3350_) == 3)
{
lean_object* v_u_3351_; 
v_u_3351_ = lean_ctor_get(v_x_3350_, 0);
lean_inc(v_u_3351_);
return v_u_3351_;
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3353_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3352_);
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_Expr_sortLevel_x21(v_x_3354_);
lean_dec_ref(v_x_3354_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3356_){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3358_ = lean_panic_fn_borrowed(v___x_3357_, v_msg_3356_);
return v___x_3358_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3361_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3362_ = lean_unsigned_to_nat(13u);
v___x_3363_ = lean_unsigned_to_nat(997u);
v___x_3364_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3365_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3366_ = l_mkPanicMessageWithDecl(v___x_3365_, v___x_3364_, v___x_3363_, v___x_3362_, v___x_3361_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3367_){
_start:
{
if (lean_obj_tag(v_x_3367_) == 9)
{
lean_object* v_a_3368_; 
v_a_3368_ = lean_ctor_get(v_x_3367_, 0);
lean_inc_ref(v_a_3368_);
return v_a_3368_;
}
else
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3370_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3369_);
return v___x_3370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Expr_litValue_x21(v_x_3371_);
lean_dec_ref(v_x_3371_);
return v_res_3372_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3373_){
_start:
{
if (lean_obj_tag(v_x_3373_) == 9)
{
lean_object* v_a_3374_; 
v_a_3374_ = lean_ctor_get(v_x_3373_, 0);
if (lean_obj_tag(v_a_3374_) == 0)
{
uint8_t v___x_3375_; 
v___x_3375_ = 1;
return v___x_3375_;
}
else
{
uint8_t v___x_3376_; 
v___x_3376_ = 0;
return v___x_3376_;
}
}
else
{
uint8_t v___x_3377_; 
v___x_3377_ = 0;
return v___x_3377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3378_){
_start:
{
uint8_t v_res_3379_; lean_object* v_r_3380_; 
v_res_3379_ = l_Lean_Expr_isRawNatLit(v_x_3378_);
lean_dec_ref(v_x_3378_);
v_r_3380_ = lean_box(v_res_3379_);
return v_r_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3381_){
_start:
{
if (lean_obj_tag(v_x_3381_) == 9)
{
lean_object* v_a_3382_; 
v_a_3382_ = lean_ctor_get(v_x_3381_, 0);
lean_inc_ref(v_a_3382_);
lean_dec_ref_known(v_x_3381_, 1);
if (lean_obj_tag(v_a_3382_) == 0)
{
lean_object* v_val_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
v_val_3383_ = lean_ctor_get(v_a_3382_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_a_3382_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v_a_3382_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_val_3383_);
lean_dec(v_a_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
lean_ctor_set_tag(v___x_3385_, 1);
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_val_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
else
{
lean_object* v___x_3391_; 
lean_dec_ref(v_a_3382_);
v___x_3391_ = lean_box(0);
return v___x_3391_;
}
}
else
{
lean_object* v___x_3392_; 
lean_dec_ref(v_x_3381_);
v___x_3392_ = lean_box(0);
return v___x_3392_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3393_){
_start:
{
if (lean_obj_tag(v_x_3393_) == 9)
{
lean_object* v_a_3394_; 
v_a_3394_ = lean_ctor_get(v_x_3393_, 0);
if (lean_obj_tag(v_a_3394_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3398_){
_start:
{
uint8_t v_res_3399_; lean_object* v_r_3400_; 
v_res_3399_ = l_Lean_Expr_isStringLit(v_x_3398_);
lean_dec_ref(v_x_3398_);
v_r_3400_ = lean_box(v_res_3399_);
return v_r_3400_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3405_){
_start:
{
if (lean_obj_tag(v_x_3405_) == 5)
{
lean_object* v_fn_3406_; 
v_fn_3406_ = lean_ctor_get(v_x_3405_, 0);
if (lean_obj_tag(v_fn_3406_) == 4)
{
lean_object* v_arg_3407_; lean_object* v_declName_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
v_arg_3407_ = lean_ctor_get(v_x_3405_, 1);
v_declName_3408_ = lean_ctor_get(v_fn_3406_, 0);
v___x_3409_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3410_ = lean_name_eq(v_declName_3408_, v___x_3409_);
if (v___x_3410_ == 0)
{
return v___x_3410_;
}
else
{
uint8_t v___x_3411_; 
v___x_3411_ = l_Lean_Expr_isRawNatLit(v_arg_3407_);
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
else
{
uint8_t v___x_3413_; 
v___x_3413_ = 0;
return v___x_3413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3414_){
_start:
{
uint8_t v_res_3415_; lean_object* v_r_3416_; 
v_res_3415_ = l_Lean_Expr_isCharLit(v_x_3414_);
lean_dec_ref(v_x_3414_);
v_r_3416_ = lean_box(v_res_3415_);
return v_r_3416_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3417_){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = lean_box(0);
v___x_3419_ = lean_panic_fn_borrowed(v___x_3418_, v_msg_3417_);
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3422_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3423_ = lean_unsigned_to_nat(17u);
v___x_3424_ = lean_unsigned_to_nat(1021u);
v___x_3425_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3426_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3427_ = l_mkPanicMessageWithDecl(v___x_3426_, v___x_3425_, v___x_3424_, v___x_3423_, v___x_3422_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3428_){
_start:
{
if (lean_obj_tag(v_x_3428_) == 4)
{
lean_object* v_declName_3429_; 
v_declName_3429_ = lean_ctor_get(v_x_3428_, 0);
lean_inc(v_declName_3429_);
return v_declName_3429_;
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3431_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3430_);
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Expr_constName_x21(v_x_3432_);
lean_dec_ref(v_x_3432_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3434_){
_start:
{
if (lean_obj_tag(v_x_3434_) == 4)
{
lean_object* v_declName_3435_; lean_object* v___x_3436_; 
v_declName_3435_ = lean_ctor_get(v_x_3434_, 0);
lean_inc(v_declName_3435_);
v___x_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3436_, 0, v_declName_3435_);
return v___x_3436_;
}
else
{
lean_object* v___x_3437_; 
v___x_3437_ = lean_box(0);
return v___x_3437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l_Lean_Expr_constName_x3f(v_x_3438_);
lean_dec_ref(v_x_3438_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3440_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_Expr_constName_x3f(v_e_3440_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_box(0);
return v___x_3442_;
}
else
{
lean_object* v_val_3443_; 
v_val_3443_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_val_3443_);
lean_dec_ref_known(v___x_3441_, 1);
return v_val_3443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_Expr_constName(v_e_3444_);
lean_dec_ref(v_e_3444_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3446_){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_panic_fn_borrowed(v___x_3447_, v_msg_3446_);
return v___x_3448_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3450_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3451_ = lean_unsigned_to_nat(18u);
v___x_3452_ = lean_unsigned_to_nat(1041u);
v___x_3453_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3454_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3455_ = l_mkPanicMessageWithDecl(v___x_3454_, v___x_3453_, v___x_3452_, v___x_3451_, v___x_3450_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3456_){
_start:
{
if (lean_obj_tag(v_x_3456_) == 4)
{
lean_object* v_us_3457_; 
v_us_3457_ = lean_ctor_get(v_x_3456_, 1);
lean_inc(v_us_3457_);
return v_us_3457_;
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3459_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3458_);
return v___x_3459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_Expr_constLevels_x21(v_x_3460_);
lean_dec_ref(v_x_3460_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3462_){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = lean_unsigned_to_nat(0u);
v___x_3464_ = lean_panic_fn_borrowed(v___x_3463_, v_msg_3462_);
return v___x_3464_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3467_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3468_ = lean_unsigned_to_nat(16u);
v___x_3469_ = lean_unsigned_to_nat(1045u);
v___x_3470_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3471_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3472_ = l_mkPanicMessageWithDecl(v___x_3471_, v___x_3470_, v___x_3469_, v___x_3468_, v___x_3467_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3473_){
_start:
{
if (lean_obj_tag(v_x_3473_) == 0)
{
lean_object* v_deBruijnIndex_3474_; 
v_deBruijnIndex_3474_ = lean_ctor_get(v_x_3473_, 0);
lean_inc(v_deBruijnIndex_3474_);
return v_deBruijnIndex_3474_;
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3476_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3475_);
return v___x_3476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_Expr_bvarIdx_x21(v_x_3477_);
lean_dec_ref(v_x_3477_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3479_){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = lean_box(0);
v___x_3481_ = lean_panic_fn_borrowed(v___x_3480_, v_msg_3479_);
return v___x_3481_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3484_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3485_ = lean_unsigned_to_nat(14u);
v___x_3486_ = lean_unsigned_to_nat(1049u);
v___x_3487_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3488_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3489_ = l_mkPanicMessageWithDecl(v___x_3488_, v___x_3487_, v___x_3486_, v___x_3485_, v___x_3484_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3490_){
_start:
{
if (lean_obj_tag(v_x_3490_) == 1)
{
lean_object* v_fvarId_3491_; 
v_fvarId_3491_ = lean_ctor_get(v_x_3490_, 0);
lean_inc(v_fvarId_3491_);
return v_fvarId_3491_;
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3493_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3492_);
return v___x_3493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Expr_fvarId_x21(v_x_3494_);
lean_dec_ref(v_x_3494_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3496_){
_start:
{
if (lean_obj_tag(v_x_3496_) == 1)
{
lean_object* v_fvarId_3497_; lean_object* v___x_3498_; 
v_fvarId_3497_ = lean_ctor_get(v_x_3496_, 0);
lean_inc(v_fvarId_3497_);
v___x_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_fvarId_3497_);
return v___x_3498_;
}
else
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_box(0);
return v___x_3499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Lean_Expr_fvarId_x3f(v_x_3500_);
lean_dec_ref(v_x_3500_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3502_){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = lean_box(0);
v___x_3504_ = lean_panic_fn_borrowed(v___x_3503_, v_msg_3502_);
return v___x_3504_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3507_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3508_ = lean_unsigned_to_nat(14u);
v___x_3509_ = lean_unsigned_to_nat(1057u);
v___x_3510_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3511_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3512_ = l_mkPanicMessageWithDecl(v___x_3511_, v___x_3510_, v___x_3509_, v___x_3508_, v___x_3507_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3513_){
_start:
{
if (lean_obj_tag(v_x_3513_) == 2)
{
lean_object* v_mvarId_3514_; 
v_mvarId_3514_ = lean_ctor_get(v_x_3513_, 0);
lean_inc(v_mvarId_3514_);
return v_mvarId_3514_;
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3516_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3515_);
return v___x_3516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_Expr_mvarId_x21(v_x_3517_);
lean_dec_ref(v_x_3517_);
return v_res_3518_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3521_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3522_ = lean_unsigned_to_nat(23u);
v___x_3523_ = lean_unsigned_to_nat(1062u);
v___x_3524_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3525_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3526_ = l_mkPanicMessageWithDecl(v___x_3525_, v___x_3524_, v___x_3523_, v___x_3522_, v___x_3521_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3527_){
_start:
{
switch(lean_obj_tag(v_x_3527_))
{
case 7:
{
lean_object* v_binderName_3528_; 
v_binderName_3528_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_binderName_3528_);
return v_binderName_3528_;
}
case 6:
{
lean_object* v_binderName_3529_; 
v_binderName_3529_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_binderName_3529_);
return v_binderName_3529_;
}
default: 
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3531_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3530_);
return v___x_3531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_Expr_bindingName_x21(v_x_3532_);
lean_dec_ref(v_x_3532_);
return v_res_3533_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3535_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3536_ = lean_unsigned_to_nat(23u);
v___x_3537_ = lean_unsigned_to_nat(1067u);
v___x_3538_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3539_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3540_ = l_mkPanicMessageWithDecl(v___x_3539_, v___x_3538_, v___x_3537_, v___x_3536_, v___x_3535_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3541_){
_start:
{
switch(lean_obj_tag(v_x_3541_))
{
case 7:
{
lean_object* v_binderType_3542_; 
v_binderType_3542_ = lean_ctor_get(v_x_3541_, 1);
lean_inc_ref(v_binderType_3542_);
return v_binderType_3542_;
}
case 6:
{
lean_object* v_binderType_3543_; 
v_binderType_3543_ = lean_ctor_get(v_x_3541_, 1);
lean_inc_ref(v_binderType_3543_);
return v_binderType_3543_;
}
default: 
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3545_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3544_);
return v___x_3545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_Expr_bindingDomain_x21(v_x_3546_);
lean_dec_ref(v_x_3546_);
return v_res_3547_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3549_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3550_ = lean_unsigned_to_nat(23u);
v___x_3551_ = lean_unsigned_to_nat(1072u);
v___x_3552_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3553_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3554_ = l_mkPanicMessageWithDecl(v___x_3553_, v___x_3552_, v___x_3551_, v___x_3550_, v___x_3549_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3555_){
_start:
{
switch(lean_obj_tag(v_x_3555_))
{
case 7:
{
lean_object* v_body_3556_; 
v_body_3556_ = lean_ctor_get(v_x_3555_, 2);
lean_inc_ref(v_body_3556_);
return v_body_3556_;
}
case 6:
{
lean_object* v_body_3557_; 
v_body_3557_ = lean_ctor_get(v_x_3555_, 2);
lean_inc_ref(v_body_3557_);
return v_body_3557_;
}
default: 
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3559_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3558_);
return v___x_3559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_Expr_bindingBody_x21(v_x_3560_);
lean_dec_ref(v_x_3560_);
return v_res_3561_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3562_){
_start:
{
uint8_t v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3563_ = 0;
v___x_3564_ = lean_box(v___x_3563_);
v___x_3565_ = lean_panic_fn_borrowed(v___x_3564_, v_msg_3562_);
lean_dec(v___x_3564_);
v___x_3566_ = lean_unbox(v___x_3565_);
lean_dec(v___x_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3567_){
_start:
{
uint8_t v_res_3568_; lean_object* v_r_3569_; 
v_res_3568_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3567_);
v_r_3569_ = lean_box(v_res_3568_);
return v_r_3569_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3571_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3572_ = lean_unsigned_to_nat(24u);
v___x_3573_ = lean_unsigned_to_nat(1077u);
v___x_3574_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3575_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3576_ = l_mkPanicMessageWithDecl(v___x_3575_, v___x_3574_, v___x_3573_, v___x_3572_, v___x_3571_);
return v___x_3576_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3577_){
_start:
{
switch(lean_obj_tag(v_x_3577_))
{
case 7:
{
uint8_t v_binderInfo_3578_; 
v_binderInfo_3578_ = lean_ctor_get_uint8(v_x_3577_, sizeof(void*)*3 + 8);
return v_binderInfo_3578_;
}
case 6:
{
uint8_t v_binderInfo_3579_; 
v_binderInfo_3579_ = lean_ctor_get_uint8(v_x_3577_, sizeof(void*)*3 + 8);
return v_binderInfo_3579_;
}
default: 
{
lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3580_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3581_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3580_);
return v___x_3581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3582_){
_start:
{
uint8_t v_res_3583_; lean_object* v_r_3584_; 
v_res_3583_ = l_Lean_Expr_bindingInfo_x21(v_x_3582_);
lean_dec_ref(v_x_3582_);
v_r_3584_ = lean_box(v_res_3583_);
return v_r_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3585_){
_start:
{
lean_object* v_binderName_3586_; 
v_binderName_3586_ = lean_ctor_get(v_x_3585_, 0);
lean_inc(v_binderName_3586_);
return v_binderName_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_Lean_Expr_forallName___redArg(v_x_3587_);
lean_dec_ref(v_x_3587_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v_binderName_3591_; 
v_binderName_3591_ = lean_ctor_get(v_x_3589_, 0);
lean_inc(v_binderName_3591_);
return v_binderName_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_Expr_forallName(v_x_3592_, v_x_3593_);
lean_dec_ref(v_x_3592_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3595_){
_start:
{
lean_object* v_binderType_3596_; 
v_binderType_3596_ = lean_ctor_get(v_x_3595_, 1);
lean_inc_ref(v_binderType_3596_);
return v_binderType_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_Expr_forallDomain___redArg(v_x_3597_);
lean_dec_ref(v_x_3597_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3599_, lean_object* v_x_3600_){
_start:
{
lean_object* v_binderType_3601_; 
v_binderType_3601_ = lean_ctor_get(v_x_3599_, 1);
lean_inc_ref(v_binderType_3601_);
return v_binderType_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3602_, lean_object* v_x_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Expr_forallDomain(v_x_3602_, v_x_3603_);
lean_dec_ref(v_x_3602_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3605_){
_start:
{
lean_object* v_body_3606_; 
v_body_3606_ = lean_ctor_get(v_x_3605_, 2);
lean_inc_ref(v_body_3606_);
return v_body_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lean_Expr_forallBody___redArg(v_x_3607_);
lean_dec_ref(v_x_3607_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3609_, lean_object* v_x_3610_){
_start:
{
lean_object* v_body_3611_; 
v_body_3611_ = lean_ctor_get(v_x_3609_, 2);
lean_inc_ref(v_body_3611_);
return v_body_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_Expr_forallBody(v_x_3612_, v_x_3613_);
lean_dec_ref(v_x_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3615_){
_start:
{
uint8_t v_binderInfo_3616_; 
v_binderInfo_3616_ = lean_ctor_get_uint8(v_x_3615_, sizeof(void*)*3 + 8);
return v_binderInfo_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3617_){
_start:
{
uint8_t v_res_3618_; lean_object* v_r_3619_; 
v_res_3618_ = l_Lean_Expr_forallInfo___redArg(v_x_3617_);
lean_dec_ref(v_x_3617_);
v_r_3619_ = lean_box(v_res_3618_);
return v_r_3619_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
uint8_t v_binderInfo_3622_; 
v_binderInfo_3622_ = lean_ctor_get_uint8(v_x_3620_, sizeof(void*)*3 + 8);
return v_binderInfo_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
uint8_t v_res_3625_; lean_object* v_r_3626_; 
v_res_3625_ = l_Lean_Expr_forallInfo(v_x_3623_, v_x_3624_);
lean_dec_ref(v_x_3623_);
v_r_3626_ = lean_box(v_res_3625_);
return v_r_3626_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3629_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3630_ = lean_unsigned_to_nat(17u);
v___x_3631_ = lean_unsigned_to_nat(1093u);
v___x_3632_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3633_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3634_ = l_mkPanicMessageWithDecl(v___x_3633_, v___x_3632_, v___x_3631_, v___x_3630_, v___x_3629_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3635_){
_start:
{
if (lean_obj_tag(v_x_3635_) == 8)
{
lean_object* v_declName_3636_; 
v_declName_3636_ = lean_ctor_get(v_x_3635_, 0);
lean_inc(v_declName_3636_);
return v_declName_3636_;
}
else
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3638_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3637_);
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_Expr_letName_x21(v_x_3639_);
lean_dec_ref(v_x_3639_);
return v_res_3640_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3642_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3643_ = lean_unsigned_to_nat(19u);
v___x_3644_ = lean_unsigned_to_nat(1097u);
v___x_3645_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3646_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3647_ = l_mkPanicMessageWithDecl(v___x_3646_, v___x_3645_, v___x_3644_, v___x_3643_, v___x_3642_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3648_){
_start:
{
if (lean_obj_tag(v_x_3648_) == 8)
{
lean_object* v_type_3649_; 
v_type_3649_ = lean_ctor_get(v_x_3648_, 1);
lean_inc_ref(v_type_3649_);
return v_type_3649_;
}
else
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3651_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3650_);
return v___x_3651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Lean_Expr_letType_x21(v_x_3652_);
lean_dec_ref(v_x_3652_);
return v_res_3653_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3655_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3656_ = lean_unsigned_to_nat(21u);
v___x_3657_ = lean_unsigned_to_nat(1101u);
v___x_3658_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3659_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3660_ = l_mkPanicMessageWithDecl(v___x_3659_, v___x_3658_, v___x_3657_, v___x_3656_, v___x_3655_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3661_){
_start:
{
if (lean_obj_tag(v_x_3661_) == 8)
{
lean_object* v_value_3662_; 
v_value_3662_ = lean_ctor_get(v_x_3661_, 2);
lean_inc_ref(v_value_3662_);
return v_value_3662_;
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3664_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3663_);
return v___x_3664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_Expr_letValue_x21(v_x_3665_);
lean_dec_ref(v_x_3665_);
return v_res_3666_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3668_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3669_ = lean_unsigned_to_nat(23u);
v___x_3670_ = lean_unsigned_to_nat(1105u);
v___x_3671_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3672_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3673_ = l_mkPanicMessageWithDecl(v___x_3672_, v___x_3671_, v___x_3670_, v___x_3669_, v___x_3668_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3674_){
_start:
{
if (lean_obj_tag(v_x_3674_) == 8)
{
lean_object* v_body_3675_; 
v_body_3675_ = lean_ctor_get(v_x_3674_, 3);
lean_inc_ref(v_body_3675_);
return v_body_3675_;
}
else
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3677_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3676_);
return v___x_3677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l_Lean_Expr_letBody_x21(v_x_3678_);
lean_dec_ref(v_x_3678_);
return v_res_3679_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3680_){
_start:
{
uint8_t v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3681_ = 0;
v___x_3682_ = lean_box(v___x_3681_);
v___x_3683_ = lean_panic_fn_borrowed(v___x_3682_, v_msg_3680_);
lean_dec(v___x_3682_);
v___x_3684_ = lean_unbox(v___x_3683_);
lean_dec(v___x_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3685_){
_start:
{
uint8_t v_res_3686_; lean_object* v_r_3687_; 
v_res_3686_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3685_);
v_r_3687_ = lean_box(v_res_3686_);
return v_r_3687_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3689_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3690_ = lean_unsigned_to_nat(27u);
v___x_3691_ = lean_unsigned_to_nat(1109u);
v___x_3692_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3693_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3694_ = l_mkPanicMessageWithDecl(v___x_3693_, v___x_3692_, v___x_3691_, v___x_3690_, v___x_3689_);
return v___x_3694_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3695_){
_start:
{
if (lean_obj_tag(v_x_3695_) == 8)
{
uint8_t v_nondep_3696_; 
v_nondep_3696_ = lean_ctor_get_uint8(v_x_3695_, sizeof(void*)*4 + 8);
return v_nondep_3696_;
}
else
{
lean_object* v___x_3697_; uint8_t v___x_3698_; 
v___x_3697_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3698_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3697_);
return v___x_3698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3699_){
_start:
{
uint8_t v_res_3700_; lean_object* v_r_3701_; 
v_res_3700_ = l_Lean_Expr_letNondep_x21(v_x_3699_);
lean_dec_ref(v_x_3699_);
v_r_3701_ = lean_box(v_res_3700_);
return v_r_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3702_){
_start:
{
if (lean_obj_tag(v_x_3702_) == 10)
{
lean_object* v_expr_3703_; 
v_expr_3703_ = lean_ctor_get(v_x_3702_, 1);
v_x_3702_ = v_expr_3703_;
goto _start;
}
else
{
lean_inc_ref(v_x_3702_);
return v_x_3702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_Expr_consumeMData(v_x_3705_);
lean_dec_ref(v_x_3705_);
return v_res_3706_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3709_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3710_ = lean_unsigned_to_nat(17u);
v___x_3711_ = lean_unsigned_to_nat(1117u);
v___x_3712_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3713_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3714_ = l_mkPanicMessageWithDecl(v___x_3713_, v___x_3712_, v___x_3711_, v___x_3710_, v___x_3709_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3715_){
_start:
{
if (lean_obj_tag(v_x_3715_) == 10)
{
lean_object* v_expr_3716_; 
v_expr_3716_ = lean_ctor_get(v_x_3715_, 1);
lean_inc_ref(v_expr_3716_);
return v_expr_3716_;
}
else
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3718_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3717_);
return v___x_3718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_Expr_mdataExpr_x21(v_x_3719_);
lean_dec_ref(v_x_3719_);
return v_res_3720_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3723_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3724_ = lean_unsigned_to_nat(18u);
v___x_3725_ = lean_unsigned_to_nat(1121u);
v___x_3726_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3727_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3728_ = l_mkPanicMessageWithDecl(v___x_3727_, v___x_3726_, v___x_3725_, v___x_3724_, v___x_3723_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3729_){
_start:
{
if (lean_obj_tag(v_x_3729_) == 11)
{
lean_object* v_struct_3730_; 
v_struct_3730_ = lean_ctor_get(v_x_3729_, 2);
lean_inc_ref(v_struct_3730_);
return v_struct_3730_;
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3732_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3731_);
return v___x_3732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_Expr_projExpr_x21(v_x_3733_);
lean_dec_ref(v_x_3733_);
return v_res_3734_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3736_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3737_ = lean_unsigned_to_nat(18u);
v___x_3738_ = lean_unsigned_to_nat(1125u);
v___x_3739_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3740_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3741_ = l_mkPanicMessageWithDecl(v___x_3740_, v___x_3739_, v___x_3738_, v___x_3737_, v___x_3736_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3742_){
_start:
{
if (lean_obj_tag(v_x_3742_) == 11)
{
lean_object* v_idx_3743_; 
v_idx_3743_ = lean_ctor_get(v_x_3742_, 1);
lean_inc(v_idx_3743_);
return v_idx_3743_;
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3745_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3744_);
return v___x_3745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Expr_projIdx_x21(v_x_3746_);
lean_dec_ref(v_x_3746_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3748_){
_start:
{
if (lean_obj_tag(v_x_3748_) == 7)
{
lean_object* v_body_3749_; 
v_body_3749_ = lean_ctor_get(v_x_3748_, 2);
v_x_3748_ = v_body_3749_;
goto _start;
}
else
{
lean_inc_ref(v_x_3748_);
return v_x_3748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l_Lean_Expr_getForallBody(v_x_3751_);
lean_dec_ref(v_x_3751_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3753_, lean_object* v_x_3754_){
_start:
{
lean_object* v_zero_3755_; uint8_t v_isZero_3756_; 
v_zero_3755_ = lean_unsigned_to_nat(0u);
v_isZero_3756_ = lean_nat_dec_eq(v_x_3753_, v_zero_3755_);
if (v_isZero_3756_ == 1)
{
lean_dec(v_x_3753_);
lean_inc_ref(v_x_3754_);
return v_x_3754_;
}
else
{
if (lean_obj_tag(v_x_3754_) == 7)
{
lean_object* v_body_3757_; lean_object* v_one_3758_; lean_object* v_n_3759_; 
v_body_3757_ = lean_ctor_get(v_x_3754_, 2);
v_one_3758_ = lean_unsigned_to_nat(1u);
v_n_3759_ = lean_nat_sub(v_x_3753_, v_one_3758_);
lean_dec(v_x_3753_);
v_x_3753_ = v_n_3759_;
v_x_3754_ = v_body_3757_;
goto _start;
}
else
{
lean_dec(v_x_3753_);
lean_inc_ref(v_x_3754_);
return v_x_3754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3761_, lean_object* v_x_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3761_, v_x_3762_);
lean_dec_ref(v_x_3762_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3764_){
_start:
{
if (lean_obj_tag(v_x_3764_) == 7)
{
lean_object* v_binderName_3765_; lean_object* v_body_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v_binderName_3765_ = lean_ctor_get(v_x_3764_, 0);
v_body_3766_ = lean_ctor_get(v_x_3764_, 2);
v___x_3767_ = l_Lean_Expr_getForallBinderNames(v_body_3766_);
lean_inc(v_binderName_3765_);
v___x_3768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3768_, 0, v_binderName_3765_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
return v___x_3768_;
}
else
{
lean_object* v___x_3769_; 
v___x_3769_ = lean_box(0);
return v___x_3769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Expr_getForallBinderNames(v_x_3770_);
lean_dec_ref(v_x_3770_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3772_){
_start:
{
switch(lean_obj_tag(v_x_3772_))
{
case 10:
{
lean_object* v_expr_3773_; 
v_expr_3773_ = lean_ctor_get(v_x_3772_, 1);
v_x_3772_ = v_expr_3773_;
goto _start;
}
case 7:
{
lean_object* v_body_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_body_3775_ = lean_ctor_get(v_x_3772_, 2);
v___x_3776_ = l_Lean_Expr_getNumHeadForalls(v_body_3775_);
v___x_3777_ = lean_unsigned_to_nat(1u);
v___x_3778_ = lean_nat_add(v___x_3776_, v___x_3777_);
lean_dec(v___x_3776_);
return v___x_3778_;
}
default: 
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_unsigned_to_nat(0u);
return v___x_3779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Lean_Expr_getNumHeadForalls(v_x_3780_);
lean_dec_ref(v_x_3780_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3782_){
_start:
{
if (lean_obj_tag(v_x_3782_) == 5)
{
lean_object* v_fn_3783_; 
v_fn_3783_ = lean_ctor_get(v_x_3782_, 0);
v_x_3782_ = v_fn_3783_;
goto _start;
}
else
{
lean_inc_ref(v_x_3782_);
return v_x_3782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_Expr_getAppFn(v_x_3785_);
lean_dec_ref(v_x_3785_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3787_){
_start:
{
switch(lean_obj_tag(v_x_3787_))
{
case 5:
{
lean_object* v_fn_3788_; 
v_fn_3788_ = lean_ctor_get(v_x_3787_, 0);
v_x_3787_ = v_fn_3788_;
goto _start;
}
case 10:
{
lean_object* v_expr_3790_; 
v_expr_3790_ = lean_ctor_get(v_x_3787_, 1);
v_x_3787_ = v_expr_3790_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3787_);
return v_x_3787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_Expr_getAppFn_x27(v_x_3792_);
lean_dec_ref(v_x_3792_);
return v_res_3793_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3794_, lean_object* v_n_3795_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_Expr_getAppFn(v_e_3794_);
if (lean_obj_tag(v___x_3796_) == 4)
{
lean_object* v_declName_3797_; uint8_t v___x_3798_; 
v_declName_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_declName_3797_);
lean_dec_ref_known(v___x_3796_, 2);
v___x_3798_ = lean_name_eq(v_declName_3797_, v_n_3795_);
lean_dec(v_declName_3797_);
return v___x_3798_;
}
else
{
uint8_t v___x_3799_; 
lean_dec_ref(v___x_3796_);
v___x_3799_ = 0;
return v___x_3799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3800_, lean_object* v_n_3801_){
_start:
{
uint8_t v_res_3802_; lean_object* v_r_3803_; 
v_res_3802_ = l_Lean_Expr_isAppOf(v_e_3800_, v_n_3801_);
lean_dec(v_n_3801_);
lean_dec_ref(v_e_3800_);
v_r_3803_ = lean_box(v_res_3802_);
return v_r_3803_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3804_, lean_object* v_x_3805_, lean_object* v_x_3806_){
_start:
{
switch(lean_obj_tag(v_x_3804_))
{
case 4:
{
lean_object* v_declName_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
v_declName_3807_ = lean_ctor_get(v_x_3804_, 0);
v___x_3808_ = lean_unsigned_to_nat(0u);
v___x_3809_ = lean_nat_dec_eq(v_x_3806_, v___x_3808_);
lean_dec(v_x_3806_);
if (v___x_3809_ == 0)
{
return v___x_3809_;
}
else
{
uint8_t v___x_3810_; 
v___x_3810_ = lean_name_eq(v_declName_3807_, v_x_3805_);
return v___x_3810_;
}
}
case 5:
{
lean_object* v_fn_3811_; lean_object* v_zero_3812_; uint8_t v_isZero_3813_; 
v_fn_3811_ = lean_ctor_get(v_x_3804_, 0);
v_zero_3812_ = lean_unsigned_to_nat(0u);
v_isZero_3813_ = lean_nat_dec_eq(v_x_3806_, v_zero_3812_);
if (v_isZero_3813_ == 0)
{
lean_object* v_one_3814_; lean_object* v_n_3815_; 
v_one_3814_ = lean_unsigned_to_nat(1u);
v_n_3815_ = lean_nat_sub(v_x_3806_, v_one_3814_);
lean_dec(v_x_3806_);
v_x_3804_ = v_fn_3811_;
v_x_3806_ = v_n_3815_;
goto _start;
}
else
{
uint8_t v___x_3817_; 
lean_dec(v_x_3806_);
v___x_3817_ = 0;
return v___x_3817_;
}
}
default: 
{
uint8_t v___x_3818_; 
lean_dec(v_x_3806_);
v___x_3818_ = 0;
return v___x_3818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3819_, lean_object* v_x_3820_, lean_object* v_x_3821_){
_start:
{
uint8_t v_res_3822_; lean_object* v_r_3823_; 
v_res_3822_ = l_Lean_Expr_isAppOfArity(v_x_3819_, v_x_3820_, v_x_3821_);
lean_dec(v_x_3820_);
lean_dec_ref(v_x_3819_);
v_r_3823_ = lean_box(v_res_3822_);
return v_r_3823_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3824_, lean_object* v_x_3825_, lean_object* v_x_3826_){
_start:
{
switch(lean_obj_tag(v_x_3824_))
{
case 10:
{
lean_object* v_expr_3827_; 
v_expr_3827_ = lean_ctor_get(v_x_3824_, 1);
v_x_3824_ = v_expr_3827_;
goto _start;
}
case 4:
{
lean_object* v_declName_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v_declName_3829_ = lean_ctor_get(v_x_3824_, 0);
v___x_3830_ = lean_unsigned_to_nat(0u);
v___x_3831_ = lean_nat_dec_eq(v_x_3826_, v___x_3830_);
lean_dec(v_x_3826_);
if (v___x_3831_ == 0)
{
return v___x_3831_;
}
else
{
uint8_t v___x_3832_; 
v___x_3832_ = lean_name_eq(v_declName_3829_, v_x_3825_);
return v___x_3832_;
}
}
case 5:
{
lean_object* v_fn_3833_; lean_object* v_zero_3834_; uint8_t v_isZero_3835_; 
v_fn_3833_ = lean_ctor_get(v_x_3824_, 0);
v_zero_3834_ = lean_unsigned_to_nat(0u);
v_isZero_3835_ = lean_nat_dec_eq(v_x_3826_, v_zero_3834_);
if (v_isZero_3835_ == 0)
{
lean_object* v_one_3836_; lean_object* v_n_3837_; 
v_one_3836_ = lean_unsigned_to_nat(1u);
v_n_3837_ = lean_nat_sub(v_x_3826_, v_one_3836_);
lean_dec(v_x_3826_);
v_x_3824_ = v_fn_3833_;
v_x_3826_ = v_n_3837_;
goto _start;
}
else
{
uint8_t v___x_3839_; 
lean_dec(v_x_3826_);
v___x_3839_ = 0;
return v___x_3839_;
}
}
default: 
{
uint8_t v___x_3840_; 
lean_dec(v_x_3826_);
v___x_3840_ = 0;
return v___x_3840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3841_, lean_object* v_x_3842_, lean_object* v_x_3843_){
_start:
{
uint8_t v_res_3844_; lean_object* v_r_3845_; 
v_res_3844_ = l_Lean_Expr_isAppOfArity_x27(v_x_3841_, v_x_3842_, v_x_3843_);
lean_dec(v_x_3842_);
lean_dec_ref(v_x_3841_);
v_r_3845_ = lean_box(v_res_3844_);
return v_r_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3846_, lean_object* v_x_3847_){
_start:
{
if (lean_obj_tag(v_x_3846_) == 5)
{
lean_object* v_fn_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v_fn_3848_ = lean_ctor_get(v_x_3846_, 0);
v___x_3849_ = lean_unsigned_to_nat(1u);
v___x_3850_ = lean_nat_add(v_x_3847_, v___x_3849_);
lean_dec(v_x_3847_);
v_x_3846_ = v_fn_3848_;
v_x_3847_ = v___x_3850_;
goto _start;
}
else
{
return v_x_3847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3852_, lean_object* v_x_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3852_, v_x_3853_);
lean_dec_ref(v_x_3852_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3855_){
_start:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = lean_unsigned_to_nat(0u);
v___x_3857_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3855_, v___x_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_Expr_getAppNumArgs(v_e_3858_);
lean_dec_ref(v_e_3858_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3860_, lean_object* v_a_3861_){
_start:
{
switch(lean_obj_tag(v_a_3860_))
{
case 10:
{
lean_object* v_expr_3862_; 
v_expr_3862_ = lean_ctor_get(v_a_3860_, 1);
v_a_3860_ = v_expr_3862_;
goto _start;
}
case 5:
{
lean_object* v_fn_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v_fn_3864_ = lean_ctor_get(v_a_3860_, 0);
v___x_3865_ = lean_unsigned_to_nat(1u);
v___x_3866_ = lean_nat_add(v_a_3861_, v___x_3865_);
lean_dec(v_a_3861_);
v_a_3860_ = v_fn_3864_;
v_a_3861_ = v___x_3866_;
goto _start;
}
default: 
{
return v_a_3861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3868_, v_a_3869_);
lean_dec_ref(v_a_3868_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3871_){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = lean_unsigned_to_nat(0u);
v___x_3873_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3871_, v___x_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3874_);
lean_dec_ref(v_e_3874_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3876_, lean_object* v_x_3877_){
_start:
{
lean_object* v_zero_3878_; uint8_t v_isZero_3879_; 
v_zero_3878_ = lean_unsigned_to_nat(0u);
v_isZero_3879_ = lean_nat_dec_eq(v_x_3876_, v_zero_3878_);
if (v_isZero_3879_ == 0)
{
if (lean_obj_tag(v_x_3877_) == 5)
{
lean_object* v_fn_3880_; lean_object* v_one_3881_; lean_object* v_n_3882_; 
v_fn_3880_ = lean_ctor_get(v_x_3877_, 0);
v_one_3881_ = lean_unsigned_to_nat(1u);
v_n_3882_ = lean_nat_sub(v_x_3876_, v_one_3881_);
lean_dec(v_x_3876_);
v_x_3876_ = v_n_3882_;
v_x_3877_ = v_fn_3880_;
goto _start;
}
else
{
lean_dec(v_x_3876_);
lean_inc_ref(v_x_3877_);
return v_x_3877_;
}
}
else
{
lean_dec(v_x_3876_);
lean_inc_ref(v_x_3877_);
return v_x_3877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3884_, lean_object* v_x_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_Expr_getBoundedAppFn(v_x_3884_, v_x_3885_);
lean_dec_ref(v_x_3885_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3887_, lean_object* v_x_3888_, lean_object* v_x_3889_){
_start:
{
if (lean_obj_tag(v_x_3887_) == 5)
{
lean_object* v_fn_3890_; lean_object* v_arg_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_fn_3890_ = lean_ctor_get(v_x_3887_, 0);
lean_inc_ref(v_fn_3890_);
v_arg_3891_ = lean_ctor_get(v_x_3887_, 1);
lean_inc_ref(v_arg_3891_);
lean_dec_ref_known(v_x_3887_, 2);
v___x_3892_ = lean_array_set(v_x_3888_, v_x_3889_, v_arg_3891_);
v___x_3893_ = lean_unsigned_to_nat(1u);
v___x_3894_ = lean_nat_sub(v_x_3889_, v___x_3893_);
lean_dec(v_x_3889_);
v_x_3887_ = v_fn_3890_;
v_x_3888_ = v___x_3892_;
v_x_3889_ = v___x_3894_;
goto _start;
}
else
{
lean_dec(v_x_3889_);
lean_dec_ref(v_x_3887_);
return v_x_3888_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3896_; lean_object* v_dummy_3897_; 
v___x_3896_ = lean_box(0);
v_dummy_3897_ = l_Lean_Expr_sort___override(v___x_3896_);
return v_dummy_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3898_){
_start:
{
lean_object* v_dummy_3899_; lean_object* v_nargs_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_dummy_3899_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3900_ = l_Lean_Expr_getAppNumArgs(v_e_3898_);
lean_inc(v_nargs_3900_);
v___x_3901_ = lean_mk_array(v_nargs_3900_, v_dummy_3899_);
v___x_3902_ = lean_unsigned_to_nat(1u);
v___x_3903_ = lean_nat_sub(v_nargs_3900_, v___x_3902_);
lean_dec(v_nargs_3900_);
v___x_3904_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3898_, v___x_3901_, v___x_3903_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3905_, lean_object* v_x_3906_, lean_object* v_x_3907_){
_start:
{
if (lean_obj_tag(v_x_3905_) == 5)
{
lean_object* v_fn_3908_; lean_object* v_arg_3909_; lean_object* v_zero_3910_; uint8_t v_isZero_3911_; 
v_fn_3908_ = lean_ctor_get(v_x_3905_, 0);
lean_inc_ref(v_fn_3908_);
v_arg_3909_ = lean_ctor_get(v_x_3905_, 1);
lean_inc_ref(v_arg_3909_);
lean_dec_ref_known(v_x_3905_, 2);
v_zero_3910_ = lean_unsigned_to_nat(0u);
v_isZero_3911_ = lean_nat_dec_eq(v_x_3907_, v_zero_3910_);
if (v_isZero_3911_ == 0)
{
lean_object* v_one_3912_; lean_object* v_n_3913_; lean_object* v___x_3914_; 
v_one_3912_ = lean_unsigned_to_nat(1u);
v_n_3913_ = lean_nat_sub(v_x_3907_, v_one_3912_);
lean_dec(v_x_3907_);
v___x_3914_ = lean_array_set(v_x_3906_, v_n_3913_, v_arg_3909_);
v_x_3905_ = v_fn_3908_;
v_x_3906_ = v___x_3914_;
v_x_3907_ = v_n_3913_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3909_);
lean_dec_ref(v_fn_3908_);
lean_dec(v_x_3907_);
return v_x_3906_;
}
}
else
{
lean_dec(v_x_3907_);
lean_dec_ref(v_x_3905_);
return v_x_3906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3916_, lean_object* v_e_3917_){
_start:
{
lean_object* v_dummy_3918_; lean_object* v___y_3920_; lean_object* v___x_3923_; uint8_t v___x_3924_; 
v_dummy_3918_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3923_ = l_Lean_Expr_getAppNumArgs(v_e_3917_);
v___x_3924_ = lean_nat_dec_le(v_maxArgs_3916_, v___x_3923_);
if (v___x_3924_ == 0)
{
lean_dec(v_maxArgs_3916_);
v___y_3920_ = v___x_3923_;
goto v___jp_3919_;
}
else
{
lean_dec(v___x_3923_);
v___y_3920_ = v_maxArgs_3916_;
goto v___jp_3919_;
}
v___jp_3919_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_inc(v___y_3920_);
v___x_3921_ = lean_mk_array(v___y_3920_, v_dummy_3918_);
v___x_3922_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3917_, v___x_3921_, v___y_3920_);
return v___x_3922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3925_, lean_object* v_x_3926_){
_start:
{
if (lean_obj_tag(v_x_3925_) == 5)
{
lean_object* v_fn_3927_; lean_object* v_arg_3928_; lean_object* v___x_3929_; 
v_fn_3927_ = lean_ctor_get(v_x_3925_, 0);
lean_inc_ref(v_fn_3927_);
v_arg_3928_ = lean_ctor_get(v_x_3925_, 1);
lean_inc_ref(v_arg_3928_);
lean_dec_ref_known(v_x_3925_, 2);
v___x_3929_ = lean_array_push(v_x_3926_, v_arg_3928_);
v_x_3925_ = v_fn_3927_;
v_x_3926_ = v___x_3929_;
goto _start;
}
else
{
lean_dec_ref(v_x_3925_);
return v_x_3926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3931_){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3932_ = l_Lean_Expr_getAppNumArgs(v_e_3931_);
v___x_3933_ = lean_mk_empty_array_with_capacity(v___x_3932_);
lean_dec(v___x_3932_);
v___x_3934_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3931_, v___x_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3935_, lean_object* v_x_3936_, lean_object* v_x_3937_, lean_object* v_x_3938_){
_start:
{
if (lean_obj_tag(v_x_3936_) == 5)
{
lean_object* v_fn_3939_; lean_object* v_arg_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_fn_3939_ = lean_ctor_get(v_x_3936_, 0);
lean_inc_ref(v_fn_3939_);
v_arg_3940_ = lean_ctor_get(v_x_3936_, 1);
lean_inc_ref(v_arg_3940_);
lean_dec_ref_known(v_x_3936_, 2);
v___x_3941_ = lean_array_set(v_x_3937_, v_x_3938_, v_arg_3940_);
v___x_3942_ = lean_unsigned_to_nat(1u);
v___x_3943_ = lean_nat_sub(v_x_3938_, v___x_3942_);
lean_dec(v_x_3938_);
v_x_3936_ = v_fn_3939_;
v_x_3937_ = v___x_3941_;
v_x_3938_ = v___x_3943_;
goto _start;
}
else
{
lean_object* v___x_3945_; 
lean_dec(v_x_3938_);
v___x_3945_ = lean_apply_2(v_k_3935_, v_x_3936_, v_x_3937_);
return v___x_3945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3946_, lean_object* v_k_3947_, lean_object* v_x_3948_, lean_object* v_x_3949_, lean_object* v_x_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_Expr_withAppAux___redArg(v_k_3947_, v_x_3948_, v_x_3949_, v_x_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3952_, lean_object* v_k_3953_){
_start:
{
lean_object* v_dummy_3954_; lean_object* v_nargs_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v_dummy_3954_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3955_ = l_Lean_Expr_getAppNumArgs(v_e_3952_);
lean_inc(v_nargs_3955_);
v___x_3956_ = lean_mk_array(v_nargs_3955_, v_dummy_3954_);
v___x_3957_ = lean_unsigned_to_nat(1u);
v___x_3958_ = lean_nat_sub(v_nargs_3955_, v___x_3957_);
lean_dec(v_nargs_3955_);
v___x_3959_ = l_Lean_Expr_withAppAux___redArg(v_k_3953_, v_e_3952_, v___x_3956_, v___x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3960_, lean_object* v_e_3961_, lean_object* v_k_3962_){
_start:
{
lean_object* v_dummy_3963_; lean_object* v_nargs_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_dummy_3963_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3964_ = l_Lean_Expr_getAppNumArgs(v_e_3961_);
lean_inc(v_nargs_3964_);
v___x_3965_ = lean_mk_array(v_nargs_3964_, v_dummy_3963_);
v___x_3966_ = lean_unsigned_to_nat(1u);
v___x_3967_ = lean_nat_sub(v_nargs_3964_, v___x_3966_);
lean_dec(v_nargs_3964_);
v___x_3968_ = l_Lean_Expr_withAppAux___redArg(v_k_3962_, v_e_3961_, v___x_3965_, v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3969_, lean_object* v_x_3970_, lean_object* v_x_3971_){
_start:
{
if (lean_obj_tag(v_x_3969_) == 5)
{
lean_object* v_fn_3972_; lean_object* v_arg_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_fn_3972_ = lean_ctor_get(v_x_3969_, 0);
lean_inc_ref(v_fn_3972_);
v_arg_3973_ = lean_ctor_get(v_x_3969_, 1);
lean_inc_ref(v_arg_3973_);
lean_dec_ref_known(v_x_3969_, 2);
v___x_3974_ = lean_array_set(v_x_3970_, v_x_3971_, v_arg_3973_);
v___x_3975_ = lean_unsigned_to_nat(1u);
v___x_3976_ = lean_nat_sub(v_x_3971_, v___x_3975_);
lean_dec(v_x_3971_);
v_x_3969_ = v_fn_3972_;
v_x_3970_ = v___x_3974_;
v_x_3971_ = v___x_3976_;
goto _start;
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
lean_dec(v_x_3971_);
v___x_3978_ = l_Lean_Expr_constName(v_x_3969_);
lean_dec_ref(v_x_3969_);
v___x_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
lean_ctor_set(v___x_3979_, 1, v_x_3970_);
return v___x_3979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3980_){
_start:
{
lean_object* v_dummy_3981_; lean_object* v_nargs_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_dummy_3981_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3982_ = l_Lean_Expr_getAppNumArgs(v_e_3980_);
lean_inc(v_nargs_3982_);
v___x_3983_ = lean_mk_array(v_nargs_3982_, v_dummy_3981_);
v___x_3984_ = lean_unsigned_to_nat(1u);
v___x_3985_ = lean_nat_sub(v_nargs_3982_, v___x_3984_);
lean_dec(v_nargs_3982_);
v___x_3986_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3980_, v___x_3983_, v___x_3985_);
return v___x_3986_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Array_instInhabited___redArg();
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_3988_){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3989_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_3990_ = lean_panic_fn_borrowed(v___x_3989_, v_msg_3988_);
return v___x_3990_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3993_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_3994_ = lean_unsigned_to_nat(27u);
v___x_3995_ = lean_unsigned_to_nat(1282u);
v___x_3996_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_3997_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3998_ = l_mkPanicMessageWithDecl(v___x_3997_, v___x_3996_, v___x_3995_, v___x_3994_, v___x_3993_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v_zero_4002_; uint8_t v_isZero_4003_; 
v_zero_4002_ = lean_unsigned_to_nat(0u);
v_isZero_4003_ = lean_nat_dec_eq(v_a_3999_, v_zero_4002_);
if (v_isZero_4003_ == 1)
{
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
return v_a_4001_;
}
else
{
if (lean_obj_tag(v_a_4000_) == 5)
{
lean_object* v_fn_4004_; lean_object* v_arg_4005_; lean_object* v_one_4006_; lean_object* v_n_4007_; lean_object* v___x_4008_; 
v_fn_4004_ = lean_ctor_get(v_a_4000_, 0);
lean_inc_ref(v_fn_4004_);
v_arg_4005_ = lean_ctor_get(v_a_4000_, 1);
lean_inc_ref(v_arg_4005_);
lean_dec_ref_known(v_a_4000_, 2);
v_one_4006_ = lean_unsigned_to_nat(1u);
v_n_4007_ = lean_nat_sub(v_a_3999_, v_one_4006_);
lean_dec(v_a_3999_);
v___x_4008_ = lean_array_set(v_a_4001_, v_n_4007_, v_arg_4005_);
v_a_3999_ = v_n_4007_;
v_a_4000_ = v_fn_4004_;
v_a_4001_ = v___x_4008_;
goto _start;
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_dec_ref(v_a_4001_);
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
v___x_4010_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4011_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4010_);
return v___x_4011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4012_, lean_object* v_n_4013_){
_start:
{
lean_object* v_dummy_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v_dummy_4014_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4013_);
v___x_4015_ = lean_mk_array(v_n_4013_, v_dummy_4014_);
v___x_4016_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4013_, v_e_4012_, v___x_4015_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4017_, lean_object* v_n_4018_){
_start:
{
lean_object* v_zero_4019_; uint8_t v_isZero_4020_; 
v_zero_4019_ = lean_unsigned_to_nat(0u);
v_isZero_4020_ = lean_nat_dec_eq(v_n_4018_, v_zero_4019_);
if (v_isZero_4020_ == 1)
{
lean_dec(v_n_4018_);
lean_inc_ref(v_e_4017_);
return v_e_4017_;
}
else
{
if (lean_obj_tag(v_e_4017_) == 5)
{
lean_object* v_fn_4021_; lean_object* v_one_4022_; lean_object* v_n_4023_; 
v_fn_4021_ = lean_ctor_get(v_e_4017_, 0);
v_one_4022_ = lean_unsigned_to_nat(1u);
v_n_4023_ = lean_nat_sub(v_n_4018_, v_one_4022_);
lean_dec(v_n_4018_);
v_e_4017_ = v_fn_4021_;
v_n_4018_ = v_n_4023_;
goto _start;
}
else
{
lean_dec(v_n_4018_);
lean_inc_ref(v_e_4017_);
return v_e_4017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4025_, lean_object* v_n_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_Expr_stripArgsN(v_e_4025_, v_n_4026_);
lean_dec_ref(v_e_4025_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4028_, lean_object* v_n_4029_){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4030_ = l_Lean_Expr_getAppNumArgs(v_e_4028_);
v___x_4031_ = lean_nat_sub(v___x_4030_, v_n_4029_);
lean_dec(v___x_4030_);
v___x_4032_ = l_Lean_Expr_stripArgsN(v_e_4028_, v___x_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4033_, lean_object* v_n_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_Expr_getAppPrefix(v_e_4033_, v_n_4034_);
lean_dec(v_n_4034_);
lean_dec_ref(v_e_4033_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4036_, lean_object* v_inst_4037_, lean_object* v_f_4038_, lean_object* v_x_4039_){
_start:
{
size_t v_sz_4040_; size_t v___x_4041_; lean_object* v___x_4042_; 
v_sz_4040_ = lean_array_size(v_args_4036_);
v___x_4041_ = ((size_t)0ULL);
v___x_4042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4037_, v_f_4038_, v_sz_4040_, v___x_4041_, v_args_4036_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4044_, lean_object* v_inst_4045_, lean_object* v_f_4046_, lean_object* v_toSeq_4047_, lean_object* v_fn_4048_, lean_object* v_args_4049_){
_start:
{
lean_object* v_map_4050_; lean_object* v___f_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v_map_4050_ = lean_ctor_get(v_toFunctor_4044_, 0);
lean_inc(v_map_4050_);
lean_dec_ref(v_toFunctor_4044_);
lean_inc(v_f_4046_);
v___f_4051_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4051_, 0, v_args_4049_);
lean_closure_set(v___f_4051_, 1, v_inst_4045_);
lean_closure_set(v___f_4051_, 2, v_f_4046_);
v___x_4052_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4053_ = lean_apply_1(v_f_4046_, v_fn_4048_);
v___x_4054_ = lean_apply_4(v_map_4050_, lean_box(0), lean_box(0), v___x_4052_, v___x_4053_);
v___x_4055_ = lean_apply_4(v_toSeq_4047_, lean_box(0), lean_box(0), v___x_4054_, v___f_4051_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4056_, lean_object* v_f_4057_, lean_object* v_e_4058_){
_start:
{
lean_object* v_toApplicative_4059_; lean_object* v_toFunctor_4060_; lean_object* v_toSeq_4061_; lean_object* v___f_4062_; lean_object* v_dummy_4063_; lean_object* v_nargs_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v_toApplicative_4059_ = lean_ctor_get(v_inst_4056_, 0);
v_toFunctor_4060_ = lean_ctor_get(v_toApplicative_4059_, 0);
lean_inc_ref(v_toFunctor_4060_);
v_toSeq_4061_ = lean_ctor_get(v_toApplicative_4059_, 2);
lean_inc(v_toSeq_4061_);
v___f_4062_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4062_, 0, v_toFunctor_4060_);
lean_closure_set(v___f_4062_, 1, v_inst_4056_);
lean_closure_set(v___f_4062_, 2, v_f_4057_);
lean_closure_set(v___f_4062_, 3, v_toSeq_4061_);
v_dummy_4063_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4064_ = l_Lean_Expr_getAppNumArgs(v_e_4058_);
lean_inc(v_nargs_4064_);
v___x_4065_ = lean_mk_array(v_nargs_4064_, v_dummy_4063_);
v___x_4066_ = lean_unsigned_to_nat(1u);
v___x_4067_ = lean_nat_sub(v_nargs_4064_, v___x_4066_);
lean_dec(v_nargs_4064_);
v___x_4068_ = l_Lean_Expr_withAppAux___redArg(v___f_4062_, v_e_4058_, v___x_4065_, v___x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4069_, lean_object* v_inst_4070_, lean_object* v_f_4071_, lean_object* v_e_4072_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = l_Lean_Expr_traverseApp___redArg(v_inst_4070_, v_f_4071_, v_e_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4074_, lean_object* v_x_4075_, lean_object* v_x_4076_){
_start:
{
if (lean_obj_tag(v_x_4075_) == 5)
{
lean_object* v_fn_4077_; lean_object* v_arg_4078_; lean_object* v___x_4079_; 
v_fn_4077_ = lean_ctor_get(v_x_4075_, 0);
lean_inc_ref(v_fn_4077_);
v_arg_4078_ = lean_ctor_get(v_x_4075_, 1);
lean_inc_ref(v_arg_4078_);
lean_dec_ref_known(v_x_4075_, 2);
v___x_4079_ = lean_array_push(v_x_4076_, v_arg_4078_);
v_x_4075_ = v_fn_4077_;
v_x_4076_ = v___x_4079_;
goto _start;
}
else
{
lean_object* v___x_4081_; 
v___x_4081_ = lean_apply_2(v_k_4074_, v_x_4075_, v_x_4076_);
return v___x_4081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4082_, lean_object* v_k_4083_, lean_object* v_x_4084_, lean_object* v_x_4085_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4083_, v_x_4084_, v_x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4087_, lean_object* v_k_4088_){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = l_Lean_Expr_getAppNumArgs(v_e_4087_);
v___x_4090_ = lean_mk_empty_array_with_capacity(v___x_4089_);
lean_dec(v___x_4089_);
v___x_4091_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4088_, v_e_4087_, v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4092_, lean_object* v_e_4093_, lean_object* v_k_4094_){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4095_ = l_Lean_Expr_getAppNumArgs(v_e_4093_);
v___x_4096_ = lean_mk_empty_array_with_capacity(v___x_4095_);
lean_dec(v___x_4095_);
v___x_4097_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4094_, v_e_4093_, v___x_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4098_, lean_object* v_x_4099_, lean_object* v_x_4100_){
_start:
{
if (lean_obj_tag(v_x_4098_) == 5)
{
lean_object* v_fn_4101_; lean_object* v_arg_4102_; lean_object* v_zero_4103_; uint8_t v_isZero_4104_; 
v_fn_4101_ = lean_ctor_get(v_x_4098_, 0);
v_arg_4102_ = lean_ctor_get(v_x_4098_, 1);
v_zero_4103_ = lean_unsigned_to_nat(0u);
v_isZero_4104_ = lean_nat_dec_eq(v_x_4099_, v_zero_4103_);
if (v_isZero_4104_ == 1)
{
lean_dec(v_x_4099_);
lean_inc_ref(v_arg_4102_);
return v_arg_4102_;
}
else
{
lean_object* v_one_4105_; lean_object* v_n_4106_; 
v_one_4105_ = lean_unsigned_to_nat(1u);
v_n_4106_ = lean_nat_sub(v_x_4099_, v_one_4105_);
lean_dec(v_x_4099_);
v_x_4098_ = v_fn_4101_;
v_x_4099_ = v_n_4106_;
goto _start;
}
}
else
{
lean_dec(v_x_4099_);
lean_inc_ref(v_x_4100_);
return v_x_4100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4108_, lean_object* v_x_4109_, lean_object* v_x_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l_Lean_Expr_getRevArgD(v_x_4108_, v_x_4109_, v_x_4110_);
lean_dec_ref(v_x_4110_);
lean_dec_ref(v_x_4108_);
return v_res_4111_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4114_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4115_ = lean_unsigned_to_nat(20u);
v___x_4116_ = lean_unsigned_to_nat(1323u);
v___x_4117_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4118_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4119_ = l_mkPanicMessageWithDecl(v___x_4118_, v___x_4117_, v___x_4116_, v___x_4115_, v___x_4114_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4120_, lean_object* v_x_4121_){
_start:
{
if (lean_obj_tag(v_x_4120_) == 5)
{
lean_object* v_fn_4122_; lean_object* v_arg_4123_; lean_object* v_zero_4124_; uint8_t v_isZero_4125_; 
v_fn_4122_ = lean_ctor_get(v_x_4120_, 0);
v_arg_4123_ = lean_ctor_get(v_x_4120_, 1);
v_zero_4124_ = lean_unsigned_to_nat(0u);
v_isZero_4125_ = lean_nat_dec_eq(v_x_4121_, v_zero_4124_);
if (v_isZero_4125_ == 1)
{
lean_dec(v_x_4121_);
lean_inc_ref(v_arg_4123_);
return v_arg_4123_;
}
else
{
lean_object* v_one_4126_; lean_object* v_n_4127_; 
v_one_4126_ = lean_unsigned_to_nat(1u);
v_n_4127_ = lean_nat_sub(v_x_4121_, v_one_4126_);
lean_dec(v_x_4121_);
v_x_4120_ = v_fn_4122_;
v_x_4121_ = v_n_4127_;
goto _start;
}
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_dec(v_x_4121_);
v___x_4129_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4130_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4129_);
return v___x_4130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4131_, lean_object* v_x_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Lean_Expr_getRevArg_x21(v_x_4131_, v_x_4132_);
lean_dec_ref(v_x_4131_);
return v_res_4133_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4135_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4136_ = lean_unsigned_to_nat(20u);
v___x_4137_ = lean_unsigned_to_nat(1330u);
v___x_4138_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4139_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4140_ = l_mkPanicMessageWithDecl(v___x_4139_, v___x_4138_, v___x_4137_, v___x_4136_, v___x_4135_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4141_, lean_object* v_x_4142_){
_start:
{
switch(lean_obj_tag(v_x_4141_))
{
case 10:
{
lean_object* v_expr_4143_; 
v_expr_4143_ = lean_ctor_get(v_x_4141_, 1);
v_x_4141_ = v_expr_4143_;
goto _start;
}
case 5:
{
lean_object* v_fn_4145_; lean_object* v_arg_4146_; lean_object* v_zero_4147_; uint8_t v_isZero_4148_; 
v_fn_4145_ = lean_ctor_get(v_x_4141_, 0);
v_arg_4146_ = lean_ctor_get(v_x_4141_, 1);
v_zero_4147_ = lean_unsigned_to_nat(0u);
v_isZero_4148_ = lean_nat_dec_eq(v_x_4142_, v_zero_4147_);
if (v_isZero_4148_ == 1)
{
lean_dec(v_x_4142_);
lean_inc_ref(v_arg_4146_);
return v_arg_4146_;
}
else
{
lean_object* v_one_4149_; lean_object* v_n_4150_; 
v_one_4149_ = lean_unsigned_to_nat(1u);
v_n_4150_ = lean_nat_sub(v_x_4142_, v_one_4149_);
lean_dec(v_x_4142_);
v_x_4141_ = v_fn_4145_;
v_x_4142_ = v_n_4150_;
goto _start;
}
}
default: 
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
lean_dec(v_x_4142_);
v___x_4152_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4153_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4152_);
return v___x_4153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4154_, lean_object* v_x_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4154_, v_x_4155_);
lean_dec_ref(v_x_4154_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4157_, lean_object* v_i_4158_, lean_object* v_n_4159_){
_start:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4160_ = lean_nat_sub(v_n_4159_, v_i_4158_);
v___x_4161_ = lean_unsigned_to_nat(1u);
v___x_4162_ = lean_nat_sub(v___x_4160_, v___x_4161_);
lean_dec(v___x_4160_);
v___x_4163_ = l_Lean_Expr_getRevArg_x21(v_e_4157_, v___x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4164_, lean_object* v_i_4165_, lean_object* v_n_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Lean_Expr_getArg_x21(v_e_4164_, v_i_4165_, v_n_4166_);
lean_dec(v_n_4166_);
lean_dec(v_i_4165_);
lean_dec_ref(v_e_4164_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4168_, lean_object* v_i_4169_, lean_object* v_n_4170_){
_start:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4171_ = lean_nat_sub(v_n_4170_, v_i_4169_);
v___x_4172_ = lean_unsigned_to_nat(1u);
v___x_4173_ = lean_nat_sub(v___x_4171_, v___x_4172_);
lean_dec(v___x_4171_);
v___x_4174_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4168_, v___x_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4175_, lean_object* v_i_4176_, lean_object* v_n_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Expr_getArg_x21_x27(v_e_4175_, v_i_4176_, v_n_4177_);
lean_dec(v_n_4177_);
lean_dec(v_i_4176_);
lean_dec_ref(v_e_4175_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4179_, lean_object* v_i_4180_, lean_object* v_v_u2080_4181_, lean_object* v_n_4182_){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4183_ = lean_nat_sub(v_n_4182_, v_i_4180_);
v___x_4184_ = lean_unsigned_to_nat(1u);
v___x_4185_ = lean_nat_sub(v___x_4183_, v___x_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = l_Lean_Expr_getRevArgD(v_e_4179_, v___x_4185_, v_v_u2080_4181_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4187_, lean_object* v_i_4188_, lean_object* v_v_u2080_4189_, lean_object* v_n_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_Expr_getArgD(v_e_4187_, v_i_4188_, v_v_u2080_4189_, v_n_4190_);
lean_dec(v_n_4190_);
lean_dec_ref(v_v_u2080_4189_);
lean_dec(v_i_4188_);
lean_dec_ref(v_e_4187_);
return v_res_4191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4192_){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; uint8_t v___x_4195_; 
v___x_4193_ = lean_unsigned_to_nat(0u);
v___x_4194_ = l_Lean_Expr_looseBVarRange(v_e_4192_);
v___x_4195_ = lean_nat_dec_lt(v___x_4193_, v___x_4194_);
lean_dec(v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4196_){
_start:
{
uint8_t v_res_4197_; lean_object* v_r_4198_; 
v_res_4197_ = l_Lean_Expr_hasLooseBVars(v_e_4196_);
lean_dec_ref(v_e_4196_);
v_r_4198_ = lean_box(v_res_4197_);
return v_r_4198_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4199_){
_start:
{
if (lean_obj_tag(v_e_4199_) == 7)
{
lean_object* v_body_4200_; uint8_t v___x_4201_; 
v_body_4200_ = lean_ctor_get(v_e_4199_, 2);
v___x_4201_ = l_Lean_Expr_hasLooseBVars(v_body_4200_);
if (v___x_4201_ == 0)
{
uint8_t v___x_4202_; 
v___x_4202_ = 1;
return v___x_4202_;
}
else
{
uint8_t v___x_4203_; 
v___x_4203_ = 0;
return v___x_4203_;
}
}
else
{
uint8_t v___x_4204_; 
v___x_4204_ = 0;
return v___x_4204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4205_){
_start:
{
uint8_t v_res_4206_; lean_object* v_r_4207_; 
v_res_4206_ = l_Lean_Expr_isArrow(v_e_4205_);
lean_dec_ref(v_e_4205_);
v_r_4207_ = lean_box(v_res_4206_);
return v_r_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4210_, lean_object* v_bvarIdx_4211_){
_start:
{
uint8_t v_res_4212_; lean_object* v_r_4213_; 
v_res_4212_ = lean_expr_has_loose_bvar(v_e_4210_, v_bvarIdx_4211_);
lean_dec(v_bvarIdx_4211_);
lean_dec_ref(v_e_4210_);
v_r_4213_ = lean_box(v_res_4212_);
return v_r_4213_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4214_, lean_object* v_bvarIdx_4215_, uint8_t v_considerRange_4216_){
_start:
{
if (lean_obj_tag(v_e_4214_) == 7)
{
lean_object* v_binderType_4217_; lean_object* v_body_4218_; uint8_t v_binderInfo_4219_; uint8_t v___x_4224_; 
v_binderType_4217_ = lean_ctor_get(v_e_4214_, 1);
v_body_4218_ = lean_ctor_get(v_e_4214_, 2);
v_binderInfo_4219_ = lean_ctor_get_uint8(v_e_4214_, sizeof(void*)*3 + 8);
v___x_4224_ = lean_expr_has_loose_bvar(v_binderType_4217_, v_bvarIdx_4215_);
if (v___x_4224_ == 0)
{
goto v___jp_4220_;
}
else
{
uint8_t v___x_4225_; 
v___x_4225_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4219_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; uint8_t v___x_4227_; 
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4218_, v___x_4226_, v_considerRange_4216_);
if (v___x_4227_ == 0)
{
goto v___jp_4220_;
}
else
{
lean_dec(v_bvarIdx_4215_);
return v___x_4227_;
}
}
else
{
lean_dec(v_bvarIdx_4215_);
return v___x_4225_;
}
}
v___jp_4220_:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4221_ = lean_unsigned_to_nat(1u);
v___x_4222_ = lean_nat_add(v_bvarIdx_4215_, v___x_4221_);
lean_dec(v_bvarIdx_4215_);
v_e_4214_ = v_body_4218_;
v_bvarIdx_4215_ = v___x_4222_;
goto _start;
}
}
else
{
if (v_considerRange_4216_ == 0)
{
lean_dec(v_bvarIdx_4215_);
return v_considerRange_4216_;
}
else
{
uint8_t v___x_4228_; 
v___x_4228_ = lean_expr_has_loose_bvar(v_e_4214_, v_bvarIdx_4215_);
lean_dec(v_bvarIdx_4215_);
return v___x_4228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4229_, lean_object* v_bvarIdx_4230_, lean_object* v_considerRange_4231_){
_start:
{
uint8_t v_considerRange_boxed_4232_; uint8_t v_res_4233_; lean_object* v_r_4234_; 
v_considerRange_boxed_4232_ = lean_unbox(v_considerRange_4231_);
v_res_4233_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4229_, v_bvarIdx_4230_, v_considerRange_boxed_4232_);
lean_dec_ref(v_e_4229_);
v_r_4234_ = lean_box(v_res_4233_);
return v_r_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4238_, lean_object* v_s_4239_, lean_object* v_d_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = lean_expr_lower_loose_bvars(v_e_4238_, v_s_4239_, v_d_4240_);
lean_dec(v_d_4240_);
lean_dec(v_s_4239_);
lean_dec_ref(v_e_4238_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4245_, lean_object* v_s_4246_, lean_object* v_d_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = lean_expr_lift_loose_bvars(v_e_4245_, v_s_4246_, v_d_4247_);
lean_dec(v_d_4247_);
lean_dec(v_s_4246_);
lean_dec_ref(v_e_4245_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4249_, lean_object* v_numParams_4250_, uint8_t v_considerRange_4251_){
_start:
{
if (lean_obj_tag(v_e_4249_) == 7)
{
lean_object* v_binderName_4252_; lean_object* v_binderType_4253_; lean_object* v_body_4254_; uint8_t v_binderInfo_4255_; lean_object* v_zero_4256_; uint8_t v_isZero_4257_; 
v_binderName_4252_ = lean_ctor_get(v_e_4249_, 0);
v_binderType_4253_ = lean_ctor_get(v_e_4249_, 1);
v_body_4254_ = lean_ctor_get(v_e_4249_, 2);
v_binderInfo_4255_ = lean_ctor_get_uint8(v_e_4249_, sizeof(void*)*3 + 8);
v_zero_4256_ = lean_unsigned_to_nat(0u);
v_isZero_4257_ = lean_nat_dec_eq(v_numParams_4250_, v_zero_4256_);
if (v_isZero_4257_ == 0)
{
lean_object* v_one_4258_; lean_object* v_n_4259_; lean_object* v_b_4260_; uint8_t v___x_4261_; 
lean_inc_ref(v_body_4254_);
lean_inc_ref(v_binderType_4253_);
lean_inc(v_binderName_4252_);
lean_dec_ref_known(v_e_4249_, 3);
v_one_4258_ = lean_unsigned_to_nat(1u);
v_n_4259_ = lean_nat_sub(v_numParams_4250_, v_one_4258_);
v_b_4260_ = l_Lean_Expr_inferImplicit(v_body_4254_, v_n_4259_, v_considerRange_4251_);
lean_dec(v_n_4259_);
v___x_4261_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4255_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Lean_Expr_forallE___override(v_binderName_4252_, v_binderType_4253_, v_b_4260_, v_binderInfo_4255_);
return v___x_4262_;
}
else
{
uint8_t v___x_4263_; 
v___x_4263_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4260_, v_zero_4256_, v_considerRange_4251_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_Expr_forallE___override(v_binderName_4252_, v_binderType_4253_, v_b_4260_, v_binderInfo_4255_);
return v___x_4264_;
}
else
{
uint8_t v___x_4265_; lean_object* v___x_4266_; 
v___x_4265_ = 1;
v___x_4266_ = l_Lean_Expr_forallE___override(v_binderName_4252_, v_binderType_4253_, v_b_4260_, v___x_4265_);
return v___x_4266_;
}
}
}
else
{
return v_e_4249_;
}
}
else
{
return v_e_4249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4267_, lean_object* v_numParams_4268_, lean_object* v_considerRange_4269_){
_start:
{
uint8_t v_considerRange_boxed_4270_; lean_object* v_res_4271_; 
v_considerRange_boxed_4270_ = lean_unbox(v_considerRange_4269_);
v_res_4271_ = l_Lean_Expr_inferImplicit(v_e_4267_, v_numParams_4268_, v_considerRange_boxed_4270_);
lean_dec(v_numParams_4268_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4272_, lean_object* v_binderInfos_x3f_4273_){
_start:
{
if (lean_obj_tag(v_e_4272_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4273_) == 1)
{
lean_object* v_binderName_4274_; lean_object* v_binderType_4275_; lean_object* v_body_4276_; uint8_t v_binderInfo_4277_; lean_object* v_head_4278_; lean_object* v_tail_4279_; lean_object* v_b_4280_; 
v_binderName_4274_ = lean_ctor_get(v_e_4272_, 0);
lean_inc(v_binderName_4274_);
v_binderType_4275_ = lean_ctor_get(v_e_4272_, 1);
lean_inc_ref(v_binderType_4275_);
v_body_4276_ = lean_ctor_get(v_e_4272_, 2);
lean_inc_ref(v_body_4276_);
v_binderInfo_4277_ = lean_ctor_get_uint8(v_e_4272_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4272_, 3);
v_head_4278_ = lean_ctor_get(v_binderInfos_x3f_4273_, 0);
v_tail_4279_ = lean_ctor_get(v_binderInfos_x3f_4273_, 1);
v_b_4280_ = l_Lean_Expr_updateForallBinderInfos(v_body_4276_, v_tail_4279_);
if (lean_obj_tag(v_head_4278_) == 0)
{
lean_object* v___x_4281_; 
v___x_4281_ = l_Lean_Expr_forallE___override(v_binderName_4274_, v_binderType_4275_, v_b_4280_, v_binderInfo_4277_);
return v___x_4281_;
}
else
{
lean_object* v_val_4282_; uint8_t v___x_4283_; lean_object* v___x_4284_; 
v_val_4282_ = lean_ctor_get(v_head_4278_, 0);
v___x_4283_ = lean_unbox(v_val_4282_);
v___x_4284_ = l_Lean_Expr_forallE___override(v_binderName_4274_, v_binderType_4275_, v_b_4280_, v___x_4283_);
return v___x_4284_;
}
}
else
{
return v_e_4272_;
}
}
else
{
return v_e_4272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4285_, lean_object* v_binderInfos_x3f_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_Lean_Expr_updateForallBinderInfos(v_e_4285_, v_binderInfos_x3f_4286_);
lean_dec(v_binderInfos_x3f_4286_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4288_, lean_object* v_binderNames_x3f_4289_){
_start:
{
switch(lean_obj_tag(v_e_4288_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4289_) == 1)
{
lean_object* v_binderName_4290_; lean_object* v_binderType_4291_; lean_object* v_body_4292_; uint8_t v_binderInfo_4293_; lean_object* v_head_4294_; lean_object* v_tail_4295_; lean_object* v_b_4296_; 
v_binderName_4290_ = lean_ctor_get(v_e_4288_, 0);
lean_inc(v_binderName_4290_);
v_binderType_4291_ = lean_ctor_get(v_e_4288_, 1);
lean_inc_ref(v_binderType_4291_);
v_body_4292_ = lean_ctor_get(v_e_4288_, 2);
lean_inc_ref(v_body_4292_);
v_binderInfo_4293_ = lean_ctor_get_uint8(v_e_4288_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4288_, 3);
v_head_4294_ = lean_ctor_get(v_binderNames_x3f_4289_, 0);
lean_inc(v_head_4294_);
v_tail_4295_ = lean_ctor_get(v_binderNames_x3f_4289_, 1);
lean_inc(v_tail_4295_);
lean_dec_ref_known(v_binderNames_x3f_4289_, 2);
v_b_4296_ = l_Lean_Expr_updateBinderNames(v_body_4292_, v_tail_4295_);
if (lean_obj_tag(v_head_4294_) == 0)
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Lean_Expr_forallE___override(v_binderName_4290_, v_binderType_4291_, v_b_4296_, v_binderInfo_4293_);
return v___x_4297_;
}
else
{
lean_object* v_val_4298_; lean_object* v___x_4299_; 
lean_dec(v_binderName_4290_);
v_val_4298_ = lean_ctor_get(v_head_4294_, 0);
lean_inc(v_val_4298_);
lean_dec_ref_known(v_head_4294_, 1);
v___x_4299_ = l_Lean_Expr_forallE___override(v_val_4298_, v_binderType_4291_, v_b_4296_, v_binderInfo_4293_);
return v___x_4299_;
}
}
else
{
lean_dec(v_binderNames_x3f_4289_);
return v_e_4288_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4289_) == 1)
{
lean_object* v_binderName_4300_; lean_object* v_binderType_4301_; lean_object* v_body_4302_; uint8_t v_binderInfo_4303_; lean_object* v_head_4304_; lean_object* v_tail_4305_; lean_object* v_b_4306_; 
v_binderName_4300_ = lean_ctor_get(v_e_4288_, 0);
lean_inc(v_binderName_4300_);
v_binderType_4301_ = lean_ctor_get(v_e_4288_, 1);
lean_inc_ref(v_binderType_4301_);
v_body_4302_ = lean_ctor_get(v_e_4288_, 2);
lean_inc_ref(v_body_4302_);
v_binderInfo_4303_ = lean_ctor_get_uint8(v_e_4288_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4288_, 3);
v_head_4304_ = lean_ctor_get(v_binderNames_x3f_4289_, 0);
lean_inc(v_head_4304_);
v_tail_4305_ = lean_ctor_get(v_binderNames_x3f_4289_, 1);
lean_inc(v_tail_4305_);
lean_dec_ref_known(v_binderNames_x3f_4289_, 2);
v_b_4306_ = l_Lean_Expr_updateBinderNames(v_body_4302_, v_tail_4305_);
if (lean_obj_tag(v_head_4304_) == 0)
{
lean_object* v___x_4307_; 
v___x_4307_ = l_Lean_Expr_lam___override(v_binderName_4300_, v_binderType_4301_, v_b_4306_, v_binderInfo_4303_);
return v___x_4307_;
}
else
{
lean_object* v_val_4308_; lean_object* v___x_4309_; 
lean_dec(v_binderName_4300_);
v_val_4308_ = lean_ctor_get(v_head_4304_, 0);
lean_inc(v_val_4308_);
lean_dec_ref_known(v_head_4304_, 1);
v___x_4309_ = l_Lean_Expr_lam___override(v_val_4308_, v_binderType_4301_, v_b_4306_, v_binderInfo_4303_);
return v___x_4309_;
}
}
else
{
lean_dec(v_binderNames_x3f_4289_);
return v_e_4288_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4289_);
return v_e_4288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4312_, lean_object* v_subst_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = lean_expr_instantiate(v_e_4312_, v_subst_4313_);
lean_dec_ref(v_subst_4313_);
lean_dec_ref(v_e_4312_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4317_, lean_object* v_subst_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = lean_expr_instantiate1(v_e_4317_, v_subst_4318_);
lean_dec_ref(v_subst_4318_);
lean_dec_ref(v_e_4317_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4322_, lean_object* v_subst_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = lean_expr_instantiate_rev(v_e_4322_, v_subst_4323_);
lean_dec_ref(v_subst_4323_);
lean_dec_ref(v_e_4322_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4329_, lean_object* v_beginIdx_4330_, lean_object* v_endIdx_4331_, lean_object* v_subst_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = lean_expr_instantiate_range(v_e_4329_, v_beginIdx_4330_, v_endIdx_4331_, v_subst_4332_);
lean_dec_ref(v_subst_4332_);
lean_dec(v_endIdx_4331_);
lean_dec(v_beginIdx_4330_);
lean_dec_ref(v_e_4329_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4338_, lean_object* v_beginIdx_4339_, lean_object* v_endIdx_4340_, lean_object* v_subst_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = lean_expr_instantiate_rev_range(v_e_4338_, v_beginIdx_4339_, v_endIdx_4340_, v_subst_4341_);
lean_dec_ref(v_subst_4341_);
lean_dec(v_endIdx_4340_);
lean_dec(v_beginIdx_4339_);
lean_dec_ref(v_e_4338_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4345_, lean_object* v_xs_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = lean_expr_abstract(v_e_4345_, v_xs_4346_);
lean_dec_ref(v_xs_4346_);
lean_dec_ref(v_e_4345_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4351_, lean_object* v_n_4352_, lean_object* v_xs_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = lean_expr_abstract_range(v_e_4351_, v_n_4352_, v_xs_4353_);
lean_dec_ref(v_xs_4353_);
lean_dec(v_n_4352_);
lean_dec_ref(v_e_4351_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4355_, lean_object* v_fvar_4356_, lean_object* v_v_4357_){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4358_ = lean_unsigned_to_nat(1u);
v___x_4359_ = lean_mk_empty_array_with_capacity(v___x_4358_);
v___x_4360_ = lean_array_push(v___x_4359_, v_fvar_4356_);
v___x_4361_ = lean_expr_abstract(v_e_4355_, v___x_4360_);
lean_dec_ref(v___x_4360_);
v___x_4362_ = lean_expr_instantiate1(v___x_4361_, v_v_4357_);
lean_dec_ref(v___x_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4363_, lean_object* v_fvar_4364_, lean_object* v_v_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_Expr_replaceFVar(v_e_4363_, v_fvar_4364_, v_v_4365_);
lean_dec_ref(v_v_4365_);
lean_dec_ref(v_e_4363_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4367_, lean_object* v_fvarId_4368_, lean_object* v_v_4369_){
_start:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4370_ = l_Lean_Expr_fvar___override(v_fvarId_4368_);
v___x_4371_ = l_Lean_Expr_replaceFVar(v_e_4367_, v___x_4370_, v_v_4369_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4372_, lean_object* v_fvarId_4373_, lean_object* v_v_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_Expr_replaceFVarId(v_e_4372_, v_fvarId_4373_, v_v_4374_);
lean_dec_ref(v_v_4374_);
lean_dec_ref(v_e_4372_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4376_, lean_object* v_fvars_4377_, lean_object* v_vs_4378_){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = lean_expr_abstract(v_e_4376_, v_fvars_4377_);
v___x_4380_ = lean_expr_instantiate_rev(v___x_4379_, v_vs_4378_);
lean_dec_ref(v___x_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4381_, lean_object* v_fvars_4382_, lean_object* v_vs_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l_Lean_Expr_replaceFVars(v_e_4381_, v_fvars_4382_, v_vs_4383_);
lean_dec_ref(v_vs_4383_);
lean_dec_ref(v_fvars_4382_);
lean_dec_ref(v_e_4381_);
return v_res_4384_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4387_){
_start:
{
switch(lean_obj_tag(v_x_4387_))
{
case 4:
{
uint8_t v___x_4388_; 
v___x_4388_ = 1;
return v___x_4388_;
}
case 3:
{
uint8_t v___x_4389_; 
v___x_4389_ = 1;
return v___x_4389_;
}
case 0:
{
uint8_t v___x_4390_; 
v___x_4390_ = 1;
return v___x_4390_;
}
case 9:
{
uint8_t v___x_4391_; 
v___x_4391_ = 1;
return v___x_4391_;
}
case 2:
{
uint8_t v___x_4392_; 
v___x_4392_ = 1;
return v___x_4392_;
}
case 1:
{
uint8_t v___x_4393_; 
v___x_4393_ = 1;
return v___x_4393_;
}
default: 
{
uint8_t v___x_4394_; 
v___x_4394_ = 0;
return v___x_4394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4395_){
_start:
{
uint8_t v_res_4396_; lean_object* v_r_4397_; 
v_res_4396_ = l_Lean_Expr_isAtomic(v_x_4395_);
lean_dec_ref(v_x_4395_);
v_r_4397_ = lean_box(v_res_4396_);
return v_r_4397_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4403_ = lean_box(0);
v___x_4404_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4405_ = l_Lean_Expr_const___override(v___x_4404_, v___x_4403_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4406_, lean_object* v_proof_4407_){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4409_ = l_Lean_mkAppB(v___x_4408_, v_pred_4406_, v_proof_4407_);
return v___x_4409_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = lean_box(0);
v___x_4415_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4416_ = l_Lean_Expr_const___override(v___x_4415_, v___x_4414_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4417_, lean_object* v_proof_4418_){
_start:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4419_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4420_ = l_Lean_mkAppB(v___x_4419_, v_pred_4417_, v_proof_4418_);
return v___x_4420_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4421_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4422_; 
v___x_4422_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4423_){
_start:
{
lean_inc_ref(v_val_4423_);
return v_val_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4424_);
lean_dec_ref(v_val_4424_);
return v_res_4425_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4428_, lean_object* v_x_4429_){
_start:
{
uint8_t v___x_4430_; 
v___x_4430_ = lean_expr_equal(v_x_4428_, v_x_4429_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4431_, lean_object* v_x_4432_){
_start:
{
uint8_t v_res_4433_; lean_object* v_r_4434_; 
v_res_4433_ = l_Lean_ExprStructEq_beq(v_x_4431_, v_x_4432_);
lean_dec_ref(v_x_4432_);
lean_dec_ref(v_x_4431_);
v_r_4434_ = lean_box(v_res_4433_);
return v_r_4434_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4435_){
_start:
{
uint64_t v___x_4436_; 
v___x_4436_ = l_Lean_Expr_hash(v_x_4435_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4437_){
_start:
{
uint64_t v_res_4438_; lean_object* v_r_4439_; 
v_res_4438_ = l_Lean_ExprStructEq_hash(v_x_4437_);
lean_dec_ref(v_x_4437_);
v_r_4439_ = lean_box_uint64(v_res_4438_);
return v_r_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4446_, lean_object* v_start_4447_, lean_object* v_b_4448_, lean_object* v_i_4449_){
_start:
{
uint8_t v___x_4450_; 
v___x_4450_ = lean_nat_dec_le(v_i_4449_, v_start_4447_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v_i_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4451_ = l_Lean_instInhabitedExpr;
v___x_4452_ = lean_unsigned_to_nat(1u);
v_i_4453_ = lean_nat_sub(v_i_4449_, v___x_4452_);
lean_dec(v_i_4449_);
v___x_4454_ = lean_array_get_borrowed(v___x_4451_, v_revArgs_4446_, v_i_4453_);
lean_inc(v___x_4454_);
v___x_4455_ = l_Lean_Expr_app___override(v_b_4448_, v___x_4454_);
v_b_4448_ = v___x_4455_;
v_i_4449_ = v_i_4453_;
goto _start;
}
else
{
lean_dec(v_i_4449_);
return v_b_4448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4457_, lean_object* v_start_4458_, lean_object* v_b_4459_, lean_object* v_i_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4457_, v_start_4458_, v_b_4459_, v_i_4460_);
lean_dec(v_start_4458_);
lean_dec_ref(v_revArgs_4457_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4462_, lean_object* v_beginIdx_4463_, lean_object* v_endIdx_4464_, lean_object* v_revArgs_4465_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4465_, v_beginIdx_4463_, v_f_4462_, v_endIdx_4464_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4467_, lean_object* v_beginIdx_4468_, lean_object* v_endIdx_4469_, lean_object* v_revArgs_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_Expr_mkAppRevRange(v_f_4467_, v_beginIdx_4468_, v_endIdx_4469_, v_revArgs_4470_);
lean_dec_ref(v_revArgs_4470_);
lean_dec(v_beginIdx_4468_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4472_, uint8_t v_useZeta_4473_, uint8_t v_preserveMData_4474_, lean_object* v_sz_4475_, lean_object* v_e_4476_, lean_object* v_i_4477_){
_start:
{
switch(lean_obj_tag(v_e_4476_))
{
case 6:
{
lean_object* v_body_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; uint8_t v___x_4486_; 
v_body_4483_ = lean_ctor_get(v_e_4476_, 2);
lean_inc_ref(v_body_4483_);
lean_dec_ref_known(v_e_4476_, 3);
v___x_4484_ = lean_unsigned_to_nat(1u);
v___x_4485_ = lean_nat_add(v_i_4477_, v___x_4484_);
lean_dec(v_i_4477_);
v___x_4486_ = lean_nat_dec_lt(v___x_4485_, v_sz_4475_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; 
lean_dec(v___x_4485_);
v___x_4487_ = lean_expr_instantiate(v_body_4483_, v_revArgs_4472_);
lean_dec_ref(v_body_4483_);
return v___x_4487_;
}
else
{
v_e_4476_ = v_body_4483_;
v_i_4477_ = v___x_4485_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4473_ == 0)
{
goto v___jp_4478_;
}
else
{
lean_object* v_value_4489_; lean_object* v_body_4490_; uint8_t v___x_4491_; 
v_value_4489_ = lean_ctor_get(v_e_4476_, 2);
v_body_4490_ = lean_ctor_get(v_e_4476_, 3);
v___x_4491_ = lean_nat_dec_lt(v_i_4477_, v_sz_4475_);
if (v___x_4491_ == 0)
{
goto v___jp_4478_;
}
else
{
lean_object* v___x_4492_; 
lean_inc_ref(v_body_4490_);
lean_inc_ref(v_value_4489_);
lean_dec_ref_known(v_e_4476_, 4);
v___x_4492_ = lean_expr_instantiate1(v_body_4490_, v_value_4489_);
lean_dec_ref(v_value_4489_);
lean_dec_ref(v_body_4490_);
v_e_4476_ = v___x_4492_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4474_ == 0)
{
lean_object* v_expr_4494_; 
v_expr_4494_ = lean_ctor_get(v_e_4476_, 1);
lean_inc_ref(v_expr_4494_);
lean_dec_ref_known(v_e_4476_, 2);
v_e_4476_ = v_expr_4494_;
goto _start;
}
else
{
goto v___jp_4478_;
}
}
default: 
{
goto v___jp_4478_;
}
}
v___jp_4478_:
{
lean_object* v_n_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v_n_4479_ = lean_nat_sub(v_sz_4475_, v_i_4477_);
lean_dec(v_i_4477_);
v___x_4480_ = lean_expr_instantiate_range(v_e_4476_, v_n_4479_, v_sz_4475_, v_revArgs_4472_);
lean_dec_ref(v_e_4476_);
v___x_4481_ = lean_unsigned_to_nat(0u);
v___x_4482_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4472_, v___x_4481_, v___x_4480_, v_n_4479_);
return v___x_4482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4496_, lean_object* v_useZeta_4497_, lean_object* v_preserveMData_4498_, lean_object* v_sz_4499_, lean_object* v_e_4500_, lean_object* v_i_4501_){
_start:
{
uint8_t v_useZeta_boxed_4502_; uint8_t v_preserveMData_boxed_4503_; lean_object* v_res_4504_; 
v_useZeta_boxed_4502_ = lean_unbox(v_useZeta_4497_);
v_preserveMData_boxed_4503_ = lean_unbox(v_preserveMData_4498_);
v_res_4504_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4496_, v_useZeta_boxed_4502_, v_preserveMData_boxed_4503_, v_sz_4499_, v_e_4500_, v_i_4501_);
lean_dec(v_sz_4499_);
lean_dec_ref(v_revArgs_4496_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4505_, lean_object* v_revArgs_4506_, uint8_t v_useZeta_4507_, uint8_t v_preserveMData_4508_){
_start:
{
lean_object* v_sz_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v_sz_4509_ = lean_array_get_size(v_revArgs_4506_);
v___x_4510_ = lean_unsigned_to_nat(0u);
v___x_4511_ = lean_nat_dec_eq(v_sz_4509_, v___x_4510_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; 
v___x_4512_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4506_, v_useZeta_4507_, v_preserveMData_4508_, v_sz_4509_, v_f_4505_, v___x_4510_);
return v___x_4512_;
}
else
{
return v_f_4505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4513_, lean_object* v_revArgs_4514_, lean_object* v_useZeta_4515_, lean_object* v_preserveMData_4516_){
_start:
{
uint8_t v_useZeta_boxed_4517_; uint8_t v_preserveMData_boxed_4518_; lean_object* v_res_4519_; 
v_useZeta_boxed_4517_ = lean_unbox(v_useZeta_4515_);
v_preserveMData_boxed_4518_ = lean_unbox(v_preserveMData_4516_);
v_res_4519_ = l_Lean_Expr_betaRev(v_f_4513_, v_revArgs_4514_, v_useZeta_boxed_4517_, v_preserveMData_boxed_4518_);
lean_dec_ref(v_revArgs_4514_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4520_, lean_object* v_args_4521_){
_start:
{
lean_object* v___x_4522_; uint8_t v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = l_Array_reverse___redArg(v_args_4521_);
v___x_4523_ = 0;
v___x_4524_ = l_Lean_Expr_betaRev(v_f_4520_, v___x_4522_, v___x_4523_, v___x_4523_);
lean_dec_ref(v___x_4522_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4525_){
_start:
{
switch(lean_obj_tag(v_x_4525_))
{
case 6:
{
lean_object* v_body_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v_body_4526_ = lean_ctor_get(v_x_4525_, 2);
v___x_4527_ = l_Lean_Expr_getNumHeadLambdas(v_body_4526_);
v___x_4528_ = lean_unsigned_to_nat(1u);
v___x_4529_ = lean_nat_add(v___x_4527_, v___x_4528_);
lean_dec(v___x_4527_);
return v___x_4529_;
}
case 10:
{
lean_object* v_expr_4530_; 
v_expr_4530_ = lean_ctor_get(v_x_4525_, 1);
v_x_4525_ = v_expr_4530_;
goto _start;
}
default: 
{
lean_object* v___x_4532_; 
v___x_4532_ = lean_unsigned_to_nat(0u);
return v___x_4532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Lean_Expr_getNumHeadLambdas(v_x_4533_);
lean_dec_ref(v_x_4533_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4535_){
_start:
{
switch(lean_obj_tag(v_x_4535_))
{
case 6:
{
lean_object* v_body_4536_; 
v_body_4536_ = lean_ctor_get(v_x_4535_, 2);
v_x_4535_ = v_body_4536_;
goto _start;
}
case 10:
{
lean_object* v_expr_4538_; 
v_expr_4538_ = lean_ctor_get(v_x_4535_, 1);
v_x_4535_ = v_expr_4538_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4535_);
return v_x_4535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean_Expr_getLambdaBody(v_x_4540_);
lean_dec_ref(v_x_4540_);
return v_res_4541_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4542_, lean_object* v_x_4543_){
_start:
{
switch(lean_obj_tag(v_x_4543_))
{
case 6:
{
uint8_t v___x_4544_; 
v___x_4544_ = 1;
return v___x_4544_;
}
case 8:
{
if (v_useZeta_4542_ == 0)
{
return v_useZeta_4542_;
}
else
{
lean_object* v_body_4545_; 
v_body_4545_ = lean_ctor_get(v_x_4543_, 3);
v_x_4543_ = v_body_4545_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4547_; 
v_expr_4547_ = lean_ctor_get(v_x_4543_, 1);
v_x_4543_ = v_expr_4547_;
goto _start;
}
default: 
{
uint8_t v___x_4549_; 
v___x_4549_ = 0;
return v___x_4549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4550_, lean_object* v_x_4551_){
_start:
{
uint8_t v_useZeta_boxed_4552_; uint8_t v_res_4553_; lean_object* v_r_4554_; 
v_useZeta_boxed_4552_ = lean_unbox(v_useZeta_4550_);
v_res_4553_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4552_, v_x_4551_);
lean_dec_ref(v_x_4551_);
v_r_4554_ = lean_box(v_res_4553_);
return v_r_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4555_){
_start:
{
lean_object* v_f_4556_; uint8_t v___x_4557_; uint8_t v___x_4558_; 
v_f_4556_ = l_Lean_Expr_getAppFn(v_e_4555_);
v___x_4557_ = 0;
v___x_4558_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4557_, v_f_4556_);
if (v___x_4558_ == 0)
{
lean_dec_ref(v_f_4556_);
return v_e_4555_;
}
else
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4559_ = l_Lean_Expr_getAppNumArgs(v_e_4555_);
v___x_4560_ = lean_mk_empty_array_with_capacity(v___x_4559_);
lean_dec(v___x_4559_);
v___x_4561_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4555_, v___x_4560_);
v___x_4562_ = l_Lean_Expr_betaRev(v_f_4556_, v___x_4561_, v___x_4557_, v___x_4557_);
lean_dec_ref(v___x_4561_);
return v___x_4562_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4563_, uint8_t v_useZeta_4564_){
_start:
{
uint8_t v___x_4565_; 
v___x_4565_ = l_Lean_Expr_isApp(v_e_4563_);
if (v___x_4565_ == 0)
{
return v___x_4565_;
}
else
{
lean_object* v___x_4566_; uint8_t v___x_4567_; 
v___x_4566_ = l_Lean_Expr_getAppFn(v_e_4563_);
v___x_4567_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4564_, v___x_4566_);
lean_dec_ref(v___x_4566_);
return v___x_4567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4568_, lean_object* v_useZeta_4569_){
_start:
{
uint8_t v_useZeta_boxed_4570_; uint8_t v_res_4571_; lean_object* v_r_4572_; 
v_useZeta_boxed_4570_ = lean_unbox(v_useZeta_4569_);
v_res_4571_ = l_Lean_Expr_isHeadBetaTarget(v_e_4568_, v_useZeta_boxed_4570_);
lean_dec_ref(v_e_4568_);
v_r_4572_ = lean_box(v_res_4571_);
return v_r_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4573_, lean_object* v_x_4574_, lean_object* v_x_4575_){
_start:
{
lean_object* v_f_4577_; 
if (lean_obj_tag(v_x_4573_) == 5)
{
lean_object* v_arg_4581_; 
v_arg_4581_ = lean_ctor_get(v_x_4573_, 1);
if (lean_obj_tag(v_arg_4581_) == 0)
{
lean_object* v_fn_4582_; lean_object* v_deBruijnIndex_4583_; lean_object* v_zero_4584_; uint8_t v_isZero_4585_; 
v_fn_4582_ = lean_ctor_get(v_x_4573_, 0);
v_deBruijnIndex_4583_ = lean_ctor_get(v_arg_4581_, 0);
v_zero_4584_ = lean_unsigned_to_nat(0u);
v_isZero_4585_ = lean_nat_dec_eq(v_x_4574_, v_zero_4584_);
if (v_isZero_4585_ == 1)
{
lean_dec(v_x_4575_);
lean_dec(v_x_4574_);
v_f_4577_ = v_x_4573_;
goto v___jp_4576_;
}
else
{
uint8_t v___x_4586_; 
lean_inc(v_deBruijnIndex_4583_);
lean_inc_ref(v_fn_4582_);
lean_dec_ref_known(v_x_4573_, 2);
v___x_4586_ = lean_nat_dec_eq(v_deBruijnIndex_4583_, v_x_4575_);
lean_dec(v_deBruijnIndex_4583_);
if (v___x_4586_ == 0)
{
lean_object* v___x_4587_; 
lean_dec_ref(v_fn_4582_);
lean_dec(v_x_4575_);
lean_dec(v_x_4574_);
v___x_4587_ = lean_box(0);
return v___x_4587_;
}
else
{
lean_object* v_one_4588_; lean_object* v_n_4589_; lean_object* v___x_4590_; 
v_one_4588_ = lean_unsigned_to_nat(1u);
v_n_4589_ = lean_nat_sub(v_x_4574_, v_one_4588_);
lean_dec(v_x_4574_);
v___x_4590_ = lean_nat_add(v_x_4575_, v_one_4588_);
lean_dec(v_x_4575_);
v_x_4573_ = v_fn_4582_;
v_x_4574_ = v_n_4589_;
v_x_4575_ = v___x_4590_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4592_; uint8_t v_isZero_4593_; 
lean_dec(v_x_4575_);
v_zero_4592_ = lean_unsigned_to_nat(0u);
v_isZero_4593_ = lean_nat_dec_eq(v_x_4574_, v_zero_4592_);
lean_dec(v_x_4574_);
if (v_isZero_4593_ == 1)
{
v_f_4577_ = v_x_4573_;
goto v___jp_4576_;
}
else
{
lean_object* v___x_4594_; 
lean_dec_ref_known(v_x_4573_, 2);
v___x_4594_ = lean_box(0);
return v___x_4594_;
}
}
}
else
{
lean_object* v_zero_4595_; uint8_t v_isZero_4596_; 
lean_dec(v_x_4575_);
v_zero_4595_ = lean_unsigned_to_nat(0u);
v_isZero_4596_ = lean_nat_dec_eq(v_x_4574_, v_zero_4595_);
lean_dec(v_x_4574_);
if (v_isZero_4596_ == 1)
{
v_f_4577_ = v_x_4573_;
goto v___jp_4576_;
}
else
{
lean_object* v___x_4597_; 
lean_dec_ref(v_x_4573_);
v___x_4597_ = lean_box(0);
return v___x_4597_;
}
}
v___jp_4576_:
{
uint8_t v___x_4578_; 
v___x_4578_ = l_Lean_Expr_hasLooseBVars(v_f_4577_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; 
v___x_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4579_, 0, v_f_4577_);
return v___x_4579_;
}
else
{
lean_object* v___x_4580_; 
lean_dec_ref(v_f_4577_);
v___x_4580_ = lean_box(0);
return v___x_4580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4598_, lean_object* v_x_4599_){
_start:
{
if (lean_obj_tag(v_x_4598_) == 6)
{
lean_object* v_body_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v_body_4600_ = lean_ctor_get(v_x_4598_, 2);
lean_inc_ref(v_body_4600_);
lean_dec_ref_known(v_x_4598_, 3);
v___x_4601_ = lean_unsigned_to_nat(1u);
v___x_4602_ = lean_nat_add(v_x_4599_, v___x_4601_);
lean_dec(v_x_4599_);
v_x_4598_ = v_body_4600_;
v_x_4599_ = v___x_4602_;
goto _start;
}
else
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4604_ = lean_unsigned_to_nat(0u);
v___x_4605_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4598_, v_x_4599_, v___x_4604_);
return v___x_4605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4606_){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4607_ = lean_unsigned_to_nat(0u);
v___x_4608_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4606_, v___x_4607_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4609_){
_start:
{
if (lean_obj_tag(v_x_4609_) == 6)
{
lean_object* v_body_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v_body_4610_ = lean_ctor_get(v_x_4609_, 2);
lean_inc_ref(v_body_4610_);
lean_dec_ref_known(v_x_4609_, 3);
v___x_4611_ = lean_unsigned_to_nat(1u);
v___x_4612_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4610_, v___x_4611_);
return v___x_4612_;
}
else
{
lean_object* v___x_4613_; 
lean_dec_ref(v_x_4609_);
v___x_4613_ = lean_box(0);
return v___x_4613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4617_){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; uint8_t v___x_4620_; 
v___x_4618_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4619_ = lean_unsigned_to_nat(2u);
v___x_4620_ = l_Lean_Expr_isAppOfArity(v_e_4617_, v___x_4618_, v___x_4619_);
if (v___x_4620_ == 0)
{
lean_object* v___x_4621_; 
v___x_4621_ = lean_box(0);
return v___x_4621_;
}
else
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = l_Lean_Expr_appArg_x21(v_e_4617_);
v___x_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
return v___x_4623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4624_);
lean_dec_ref(v_e_4624_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4629_){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; uint8_t v___x_4632_; 
v___x_4630_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4636_);
lean_dec_ref(v_e_4636_);
return v_res_4637_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4641_){
_start:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; uint8_t v___x_4644_; 
v___x_4642_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4643_ = lean_unsigned_to_nat(1u);
v___x_4644_ = l_Lean_Expr_isAppOfArity(v_e_4641_, v___x_4642_, v___x_4643_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4645_){
_start:
{
uint8_t v_res_4646_; lean_object* v_r_4647_; 
v_res_4646_ = l_Lean_Expr_isOutParam(v_e_4645_);
lean_dec_ref(v_e_4645_);
v_r_4647_ = lean_box(v_res_4646_);
return v_r_4647_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4651_){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; uint8_t v___x_4654_; 
v___x_4652_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4653_ = lean_unsigned_to_nat(1u);
v___x_4654_ = l_Lean_Expr_isAppOfArity(v_e_4651_, v___x_4652_, v___x_4653_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4655_){
_start:
{
uint8_t v_res_4656_; lean_object* v_r_4657_; 
v_res_4656_ = l_Lean_Expr_isSemiOutParam(v_e_4655_);
lean_dec_ref(v_e_4655_);
v_r_4657_ = lean_box(v_res_4656_);
return v_r_4657_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4658_){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v___x_4659_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4660_ = lean_unsigned_to_nat(2u);
v___x_4661_ = l_Lean_Expr_isAppOfArity(v_e_4658_, v___x_4659_, v___x_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4662_){
_start:
{
uint8_t v_res_4663_; lean_object* v_r_4664_; 
v_res_4663_ = l_Lean_Expr_isOptParam(v_e_4662_);
lean_dec_ref(v_e_4662_);
v_r_4664_ = lean_box(v_res_4663_);
return v_r_4664_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4665_){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; 
v___x_4666_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4667_ = lean_unsigned_to_nat(2u);
v___x_4668_ = l_Lean_Expr_isAppOfArity(v_e_4665_, v___x_4666_, v___x_4667_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4669_){
_start:
{
uint8_t v_res_4670_; lean_object* v_r_4671_; 
v_res_4670_ = l_Lean_Expr_isAutoParam(v_e_4669_);
lean_dec_ref(v_e_4669_);
v_r_4671_ = lean_box(v_res_4670_);
return v_r_4671_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4672_){
_start:
{
lean_object* v___x_4673_; 
v___x_4673_ = l_Lean_Expr_getAppFn(v_e_4672_);
if (lean_obj_tag(v___x_4673_) == 4)
{
lean_object* v_declName_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; 
v_declName_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_declName_4674_);
lean_dec_ref_known(v___x_4673_, 2);
v___x_4675_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4676_ = lean_name_eq(v_declName_4674_, v___x_4675_);
if (v___x_4676_ == 0)
{
lean_object* v___x_4677_; uint8_t v___x_4678_; 
v___x_4677_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4678_ = lean_name_eq(v_declName_4674_, v___x_4677_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4679_; uint8_t v___x_4680_; 
v___x_4679_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4680_ = lean_name_eq(v_declName_4674_, v___x_4679_);
if (v___x_4680_ == 0)
{
lean_object* v___x_4681_; uint8_t v___x_4682_; 
v___x_4681_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4682_ = lean_name_eq(v_declName_4674_, v___x_4681_);
lean_dec(v_declName_4674_);
return v___x_4682_;
}
else
{
lean_dec(v_declName_4674_);
return v___x_4680_;
}
}
else
{
lean_dec(v_declName_4674_);
return v___x_4678_;
}
}
else
{
lean_dec(v_declName_4674_);
return v___x_4676_;
}
}
else
{
uint8_t v___x_4683_; 
lean_dec_ref(v___x_4673_);
v___x_4683_ = 0;
return v___x_4683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4684_){
_start:
{
uint8_t v_res_4685_; lean_object* v_r_4686_; 
v_res_4685_ = l_Lean_Expr_isTypeAnnotation(v_e_4684_);
lean_dec_ref(v_e_4684_);
v_r_4686_ = lean_box(v_res_4685_);
return v_r_4686_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4687_){
_start:
{
if (lean_obj_tag(v_e_4687_) == 5)
{
lean_object* v_fn_4688_; 
v_fn_4688_ = lean_ctor_get(v_e_4687_, 0);
switch(lean_obj_tag(v_fn_4688_))
{
case 4:
{
lean_object* v_arg_4689_; lean_object* v_declName_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; 
v_arg_4689_ = lean_ctor_get(v_e_4687_, 1);
v_declName_4690_ = lean_ctor_get(v_fn_4688_, 0);
v___x_4691_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4692_ = lean_name_eq(v_declName_4690_, v___x_4691_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; uint8_t v___x_4694_; 
v___x_4693_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4694_ = lean_name_eq(v_declName_4690_, v___x_4693_);
if (v___x_4694_ == 0)
{
return v_e_4687_;
}
else
{
lean_inc_ref(v_arg_4689_);
lean_dec_ref_known(v_e_4687_, 2);
v_e_4687_ = v_arg_4689_;
goto _start;
}
}
else
{
lean_inc_ref(v_arg_4689_);
lean_dec_ref_known(v_e_4687_, 2);
v_e_4687_ = v_arg_4689_;
goto _start;
}
}
case 5:
{
lean_object* v_fn_4697_; 
v_fn_4697_ = lean_ctor_get(v_fn_4688_, 0);
if (lean_obj_tag(v_fn_4697_) == 4)
{
lean_object* v_arg_4698_; lean_object* v_declName_4699_; lean_object* v___x_4700_; uint8_t v___x_4701_; 
v_arg_4698_ = lean_ctor_get(v_fn_4688_, 1);
v_declName_4699_ = lean_ctor_get(v_fn_4697_, 0);
v___x_4700_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4701_ = lean_name_eq(v_declName_4699_, v___x_4700_);
if (v___x_4701_ == 0)
{
lean_object* v___x_4702_; uint8_t v___x_4703_; 
v___x_4702_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4703_ = lean_name_eq(v_declName_4699_, v___x_4702_);
if (v___x_4703_ == 0)
{
return v_e_4687_;
}
else
{
lean_inc_ref(v_arg_4698_);
lean_dec_ref_known(v_e_4687_, 2);
v_e_4687_ = v_arg_4698_;
goto _start;
}
}
else
{
lean_inc_ref(v_arg_4698_);
lean_dec_ref_known(v_e_4687_, 2);
v_e_4687_ = v_arg_4698_;
goto _start;
}
}
else
{
return v_e_4687_;
}
}
default: 
{
return v_e_4687_;
}
}
}
else
{
return v_e_4687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4706_){
_start:
{
switch(lean_obj_tag(v_e_4706_))
{
case 10:
{
lean_object* v_expr_4707_; 
v_expr_4707_ = lean_ctor_get(v_e_4706_, 1);
v_e_4706_ = v_expr_4707_;
goto _start;
}
case 5:
{
lean_object* v_fn_4709_; 
v_fn_4709_ = lean_ctor_get(v_e_4706_, 0);
switch(lean_obj_tag(v_fn_4709_))
{
case 4:
{
lean_object* v_arg_4710_; lean_object* v_declName_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v_arg_4710_ = lean_ctor_get(v_e_4706_, 1);
v_declName_4711_ = lean_ctor_get(v_fn_4709_, 0);
v___x_4712_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4713_ = lean_name_eq(v_declName_4711_, v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; uint8_t v___x_4715_; 
v___x_4714_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4715_ = lean_name_eq(v_declName_4711_, v___x_4714_);
if (v___x_4715_ == 0)
{
lean_inc_ref(v_e_4706_);
return v_e_4706_;
}
else
{
v_e_4706_ = v_arg_4710_;
goto _start;
}
}
else
{
v_e_4706_ = v_arg_4710_;
goto _start;
}
}
case 5:
{
lean_object* v_fn_4718_; 
v_fn_4718_ = lean_ctor_get(v_fn_4709_, 0);
if (lean_obj_tag(v_fn_4718_) == 4)
{
lean_object* v_arg_4719_; lean_object* v_declName_4720_; lean_object* v___x_4721_; uint8_t v___x_4722_; 
v_arg_4719_ = lean_ctor_get(v_fn_4709_, 1);
v_declName_4720_ = lean_ctor_get(v_fn_4718_, 0);
v___x_4721_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4722_ = lean_name_eq(v_declName_4720_, v___x_4721_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4723_; uint8_t v___x_4724_; 
v___x_4723_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4724_ = lean_name_eq(v_declName_4720_, v___x_4723_);
if (v___x_4724_ == 0)
{
lean_inc_ref(v_e_4706_);
return v_e_4706_;
}
else
{
v_e_4706_ = v_arg_4719_;
goto _start;
}
}
else
{
v_e_4706_ = v_arg_4719_;
goto _start;
}
}
else
{
lean_inc_ref(v_e_4706_);
return v_e_4706_;
}
}
default: 
{
lean_inc_ref(v_e_4706_);
return v_e_4706_;
}
}
}
default: 
{
lean_inc_ref(v_e_4706_);
return v_e_4706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations___boxed(lean_object* v_e_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_Lean_Expr_cleanupAnnotations(v_e_4727_);
lean_dec_ref(v_e_4727_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4729_){
_start:
{
lean_object* v_fn_4730_; lean_object* v___x_4731_; 
v_fn_4730_ = lean_ctor_get(v_e_4729_, 0);
v___x_4731_ = l_Lean_Expr_cleanupAnnotations(v_fn_4730_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg___boxed(lean_object* v_e_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4732_);
lean_dec_ref(v_e_4732_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4734_, lean_object* v_h_4735_){
_start:
{
lean_object* v___x_4736_; 
v___x_4736_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4734_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___boxed(lean_object* v_e_4737_, lean_object* v_h_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l_Lean_Expr_appFnCleanup(v_e_4737_, v_h_4738_);
lean_dec_ref(v_e_4737_);
return v_res_4739_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4743_){
_start:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; uint8_t v___x_4746_; 
v___x_4744_ = l_Lean_Expr_cleanupAnnotations(v_e_4743_);
v___x_4745_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4746_ = l_Lean_Expr_isConstOf(v___x_4744_, v___x_4745_);
lean_dec_ref(v___x_4744_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4747_){
_start:
{
uint8_t v_res_4748_; lean_object* v_r_4749_; 
v_res_4748_ = l_Lean_Expr_isFalse(v_e_4747_);
lean_dec_ref(v_e_4747_);
v_r_4749_ = lean_box(v_res_4748_);
return v_r_4749_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4753_){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; 
v___x_4754_ = l_Lean_Expr_cleanupAnnotations(v_e_4753_);
v___x_4755_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4756_ = l_Lean_Expr_isConstOf(v___x_4754_, v___x_4755_);
lean_dec_ref(v___x_4754_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4757_){
_start:
{
uint8_t v_res_4758_; lean_object* v_r_4759_; 
v_res_4758_ = l_Lean_Expr_isTrue(v_e_4757_);
lean_dec_ref(v_e_4757_);
v_r_4759_ = lean_box(v_res_4758_);
return v_r_4759_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4765_){
_start:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4766_ = l_Lean_Expr_cleanupAnnotations(v_e_4765_);
v___x_4767_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__2));
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
lean_dec_ref(v_e_4769_);
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
lean_dec_ref(v_e_4779_);
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
lean_object* v___x_4794_; 
lean_dec_ref(v_e_x27_4791_);
v___x_4794_ = lean_unsigned_to_nat(0u);
return v___x_4794_;
}
}
else
{
lean_object* v___x_4795_; 
v___x_4795_ = l_Lean_Expr_headBeta(v_x_4782_);
v_x_4782_ = v___x_4795_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4797_){
_start:
{
lean_object* v___x_4798_; uint8_t v___x_4799_; 
v___x_4798_ = l_Lean_Expr_cleanupAnnotations(v_e_4797_);
v___x_4799_ = l_Lean_Expr_isApp(v___x_4798_);
if (v___x_4799_ == 0)
{
lean_object* v___x_4800_; 
lean_dec_ref(v___x_4798_);
v___x_4800_ = lean_box(0);
return v___x_4800_;
}
else
{
lean_object* v___x_4801_; uint8_t v___x_4802_; 
v___x_4801_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4798_);
lean_dec_ref(v___x_4798_);
v___x_4802_ = l_Lean_Expr_isApp(v___x_4801_);
if (v___x_4802_ == 0)
{
lean_object* v___x_4803_; 
lean_dec_ref(v___x_4801_);
v___x_4803_ = lean_box(0);
return v___x_4803_;
}
else
{
lean_object* v_arg_4804_; lean_object* v___x_4805_; uint8_t v___x_4806_; 
v_arg_4804_ = lean_ctor_get(v___x_4801_, 1);
lean_inc_ref(v_arg_4804_);
v___x_4805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4801_);
lean_dec_ref(v___x_4801_);
v___x_4806_ = l_Lean_Expr_isApp(v___x_4805_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; 
lean_dec_ref(v___x_4805_);
lean_dec_ref(v_arg_4804_);
v___x_4807_ = lean_box(0);
return v___x_4807_;
}
else
{
lean_object* v___x_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v___x_4808_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4805_);
lean_dec_ref(v___x_4805_);
v___x_4809_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4810_ = l_Lean_Expr_isConstOf(v___x_4808_, v___x_4809_);
lean_dec_ref(v___x_4808_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; 
lean_dec_ref(v_arg_4804_);
v___x_4811_ = lean_box(0);
return v___x_4811_;
}
else
{
if (lean_obj_tag(v_arg_4804_) == 9)
{
lean_object* v_a_4812_; 
v_a_4812_ = lean_ctor_get(v_arg_4804_, 0);
lean_inc_ref(v_a_4812_);
lean_dec_ref_known(v_arg_4804_, 1);
if (lean_obj_tag(v_a_4812_) == 0)
{
lean_object* v_val_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
v_val_4813_ = lean_ctor_get(v_a_4812_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v_a_4812_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v_a_4812_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_val_4813_);
lean_dec(v_a_4812_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
lean_ctor_set_tag(v___x_4815_, 1);
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_val_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
else
{
lean_object* v___x_4821_; 
lean_dec_ref(v_a_4812_);
v___x_4821_ = lean_box(0);
return v___x_4821_;
}
}
else
{
lean_object* v___x_4822_; 
lean_dec_ref(v_arg_4804_);
v___x_4822_ = lean_box(0);
return v___x_4822_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f___boxed(lean_object* v_e_4823_){
_start:
{
lean_object* v_res_4824_; 
v_res_4824_ = l_Lean_Expr_nat_x3f(v_e_4823_);
lean_dec_ref(v_e_4823_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4830_){
_start:
{
lean_object* v___x_4843_; uint8_t v___x_4844_; 
v___x_4843_ = l_Lean_Expr_cleanupAnnotations(v_e_4830_);
v___x_4844_ = l_Lean_Expr_isApp(v___x_4843_);
if (v___x_4844_ == 0)
{
lean_dec_ref(v___x_4843_);
goto v___jp_4831_;
}
else
{
lean_object* v_arg_4845_; lean_object* v___x_4846_; uint8_t v___x_4847_; 
v_arg_4845_ = lean_ctor_get(v___x_4843_, 1);
lean_inc_ref(v_arg_4845_);
v___x_4846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4843_);
lean_dec_ref(v___x_4843_);
v___x_4847_ = l_Lean_Expr_isApp(v___x_4846_);
if (v___x_4847_ == 0)
{
lean_dec_ref(v___x_4846_);
lean_dec_ref(v_arg_4845_);
goto v___jp_4831_;
}
else
{
lean_object* v___x_4848_; uint8_t v___x_4849_; 
v___x_4848_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4846_);
lean_dec_ref(v___x_4846_);
v___x_4849_ = l_Lean_Expr_isApp(v___x_4848_);
if (v___x_4849_ == 0)
{
lean_dec_ref(v___x_4848_);
lean_dec_ref(v_arg_4845_);
goto v___jp_4831_;
}
else
{
lean_object* v___x_4850_; lean_object* v___x_4851_; uint8_t v___x_4852_; 
v___x_4850_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4848_);
lean_dec_ref(v___x_4848_);
v___x_4851_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4852_ = l_Lean_Expr_isConstOf(v___x_4850_, v___x_4851_);
lean_dec_ref(v___x_4850_);
if (v___x_4852_ == 0)
{
lean_dec_ref(v_arg_4845_);
goto v___jp_4831_;
}
else
{
lean_object* v___x_4853_; 
v___x_4853_ = l_Lean_Expr_nat_x3f(v_arg_4845_);
lean_dec_ref(v_arg_4845_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v___x_4854_; 
v___x_4854_ = lean_box(0);
return v___x_4854_;
}
else
{
lean_object* v_val_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4867_; 
v_val_4855_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4857_ = v___x_4853_;
v_isShared_4858_ = v_isSharedCheck_4867_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_val_4855_);
lean_dec(v___x_4853_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4867_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4859_ = lean_unsigned_to_nat(0u);
v___x_4860_ = lean_nat_dec_eq(v_val_4855_, v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4864_; 
v___x_4861_ = lean_nat_to_int(v_val_4855_);
v___x_4862_ = lean_int_neg(v___x_4861_);
lean_dec(v___x_4861_);
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 0, v___x_4862_);
v___x_4864_ = v___x_4857_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v___x_4862_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
else
{
lean_object* v___x_4866_; 
lean_del_object(v___x_4857_);
lean_dec(v_val_4855_);
v___x_4866_ = lean_box(0);
return v___x_4866_;
}
}
}
}
}
}
}
v___jp_4831_:
{
lean_object* v___x_4832_; 
v___x_4832_ = l_Lean_Expr_nat_x3f(v_e_4830_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v___x_4833_; 
v___x_4833_ = lean_box(0);
return v___x_4833_;
}
else
{
lean_object* v_val_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4842_; 
v_val_4834_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4836_ = v___x_4832_;
v_isShared_4837_ = v_isSharedCheck_4842_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_val_4834_);
lean_dec(v___x_4832_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4842_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4838_; lean_object* v___x_4840_; 
v___x_4838_ = lean_nat_to_int(v_val_4834_);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 0, v___x_4838_);
v___x_4840_ = v___x_4836_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4838_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f___boxed(lean_object* v_e_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_Lean_Expr_int_x3f(v_e_4868_);
lean_dec_ref(v_e_4868_);
return v_res_4869_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4870_, lean_object* v_e_4871_){
_start:
{
uint8_t v___x_4872_; lean_object* v_d_4874_; lean_object* v_b_4875_; 
v___x_4872_ = l_Lean_Expr_hasFVar(v_e_4871_);
if (v___x_4872_ == 0)
{
lean_dec_ref(v_e_4871_);
lean_dec_ref(v_p_4870_);
return v___x_4872_;
}
else
{
switch(lean_obj_tag(v_e_4871_))
{
case 7:
{
lean_object* v_binderType_4878_; lean_object* v_body_4879_; 
v_binderType_4878_ = lean_ctor_get(v_e_4871_, 1);
lean_inc_ref(v_binderType_4878_);
v_body_4879_ = lean_ctor_get(v_e_4871_, 2);
lean_inc_ref(v_body_4879_);
lean_dec_ref_known(v_e_4871_, 3);
v_d_4874_ = v_binderType_4878_;
v_b_4875_ = v_body_4879_;
goto v___jp_4873_;
}
case 6:
{
lean_object* v_binderType_4880_; lean_object* v_body_4881_; 
v_binderType_4880_ = lean_ctor_get(v_e_4871_, 1);
lean_inc_ref(v_binderType_4880_);
v_body_4881_ = lean_ctor_get(v_e_4871_, 2);
lean_inc_ref(v_body_4881_);
lean_dec_ref_known(v_e_4871_, 3);
v_d_4874_ = v_binderType_4880_;
v_b_4875_ = v_body_4881_;
goto v___jp_4873_;
}
case 10:
{
lean_object* v_expr_4882_; 
v_expr_4882_ = lean_ctor_get(v_e_4871_, 1);
lean_inc_ref(v_expr_4882_);
lean_dec_ref_known(v_e_4871_, 2);
v_e_4871_ = v_expr_4882_;
goto _start;
}
case 8:
{
lean_object* v_type_4884_; lean_object* v_value_4885_; lean_object* v_body_4886_; uint8_t v___x_4887_; 
v_type_4884_ = lean_ctor_get(v_e_4871_, 1);
lean_inc_ref(v_type_4884_);
v_value_4885_ = lean_ctor_get(v_e_4871_, 2);
lean_inc_ref(v_value_4885_);
v_body_4886_ = lean_ctor_get(v_e_4871_, 3);
lean_inc_ref(v_body_4886_);
lean_dec_ref_known(v_e_4871_, 4);
lean_inc_ref(v_p_4870_);
v___x_4887_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4870_, v_type_4884_);
if (v___x_4887_ == 0)
{
uint8_t v___x_4888_; 
lean_inc_ref(v_p_4870_);
v___x_4888_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4870_, v_value_4885_);
if (v___x_4888_ == 0)
{
v_e_4871_ = v_body_4886_;
goto _start;
}
else
{
lean_dec_ref(v_body_4886_);
lean_dec_ref(v_p_4870_);
return v___x_4872_;
}
}
else
{
lean_dec_ref(v_body_4886_);
lean_dec_ref(v_value_4885_);
lean_dec_ref(v_p_4870_);
return v___x_4872_;
}
}
case 5:
{
lean_object* v_fn_4890_; lean_object* v_arg_4891_; uint8_t v___x_4892_; 
v_fn_4890_ = lean_ctor_get(v_e_4871_, 0);
lean_inc_ref(v_fn_4890_);
v_arg_4891_ = lean_ctor_get(v_e_4871_, 1);
lean_inc_ref(v_arg_4891_);
lean_dec_ref_known(v_e_4871_, 2);
lean_inc_ref(v_p_4870_);
v___x_4892_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4870_, v_fn_4890_);
if (v___x_4892_ == 0)
{
v_e_4871_ = v_arg_4891_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4891_);
lean_dec_ref(v_p_4870_);
return v___x_4872_;
}
}
case 11:
{
lean_object* v_struct_4894_; 
v_struct_4894_ = lean_ctor_get(v_e_4871_, 2);
lean_inc_ref(v_struct_4894_);
lean_dec_ref_known(v_e_4871_, 3);
v_e_4871_ = v_struct_4894_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4896_; lean_object* v___x_4897_; uint8_t v___x_4898_; 
v_fvarId_4896_ = lean_ctor_get(v_e_4871_, 0);
lean_inc(v_fvarId_4896_);
lean_dec_ref_known(v_e_4871_, 1);
v___x_4897_ = lean_apply_1(v_p_4870_, v_fvarId_4896_);
v___x_4898_ = lean_unbox(v___x_4897_);
return v___x_4898_;
}
default: 
{
uint8_t v___x_4899_; 
lean_dec_ref(v_e_4871_);
lean_dec_ref(v_p_4870_);
v___x_4899_ = 0;
return v___x_4899_;
}
}
}
v___jp_4873_:
{
uint8_t v___x_4876_; 
lean_inc_ref(v_p_4870_);
v___x_4876_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4870_, v_d_4874_);
if (v___x_4876_ == 0)
{
v_e_4871_ = v_b_4875_;
goto _start;
}
else
{
lean_dec_ref(v_b_4875_);
lean_dec_ref(v_p_4870_);
return v___x_4872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4900_, lean_object* v_e_4901_){
_start:
{
uint8_t v_res_4902_; lean_object* v_r_4903_; 
v_res_4902_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4900_, v_e_4901_);
v_r_4903_ = lean_box(v_res_4902_);
return v_r_4903_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4904_, lean_object* v_p_4905_){
_start:
{
uint8_t v___x_4906_; 
v___x_4906_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4905_, v_e_4904_);
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4907_, lean_object* v_p_4908_){
_start:
{
uint8_t v_res_4909_; lean_object* v_r_4910_; 
v_res_4909_ = l_Lean_Expr_hasAnyFVar(v_e_4907_, v_p_4908_);
v_r_4910_ = lean_box(v_res_4909_);
return v_r_4910_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4911_, lean_object* v_e_4912_){
_start:
{
uint8_t v___x_4913_; lean_object* v_d_4915_; lean_object* v_b_4916_; 
v___x_4913_ = l_Lean_Expr_hasFVar(v_e_4912_);
if (v___x_4913_ == 0)
{
return v___x_4913_;
}
else
{
switch(lean_obj_tag(v_e_4912_))
{
case 7:
{
lean_object* v_binderType_4919_; lean_object* v_body_4920_; 
v_binderType_4919_ = lean_ctor_get(v_e_4912_, 1);
v_body_4920_ = lean_ctor_get(v_e_4912_, 2);
v_d_4915_ = v_binderType_4919_;
v_b_4916_ = v_body_4920_;
goto v___jp_4914_;
}
case 6:
{
lean_object* v_binderType_4921_; lean_object* v_body_4922_; 
v_binderType_4921_ = lean_ctor_get(v_e_4912_, 1);
v_body_4922_ = lean_ctor_get(v_e_4912_, 2);
v_d_4915_ = v_binderType_4921_;
v_b_4916_ = v_body_4922_;
goto v___jp_4914_;
}
case 10:
{
lean_object* v_expr_4923_; 
v_expr_4923_ = lean_ctor_get(v_e_4912_, 1);
v_e_4912_ = v_expr_4923_;
goto _start;
}
case 8:
{
lean_object* v_type_4925_; lean_object* v_value_4926_; lean_object* v_body_4927_; uint8_t v___x_4928_; 
v_type_4925_ = lean_ctor_get(v_e_4912_, 1);
v_value_4926_ = lean_ctor_get(v_e_4912_, 2);
v_body_4927_ = lean_ctor_get(v_e_4912_, 3);
v___x_4928_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4911_, v_type_4925_);
if (v___x_4928_ == 0)
{
uint8_t v___x_4929_; 
v___x_4929_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4911_, v_value_4926_);
if (v___x_4929_ == 0)
{
v_e_4912_ = v_body_4927_;
goto _start;
}
else
{
return v___x_4913_;
}
}
else
{
return v___x_4913_;
}
}
case 5:
{
lean_object* v_fn_4931_; lean_object* v_arg_4932_; uint8_t v___x_4933_; 
v_fn_4931_ = lean_ctor_get(v_e_4912_, 0);
v_arg_4932_ = lean_ctor_get(v_e_4912_, 1);
v___x_4933_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4911_, v_fn_4931_);
if (v___x_4933_ == 0)
{
v_e_4912_ = v_arg_4932_;
goto _start;
}
else
{
return v___x_4913_;
}
}
case 11:
{
lean_object* v_struct_4935_; 
v_struct_4935_ = lean_ctor_get(v_e_4912_, 2);
v_e_4912_ = v_struct_4935_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4937_; uint8_t v___x_4938_; 
v_fvarId_4937_ = lean_ctor_get(v_e_4912_, 0);
v___x_4938_ = lean_name_eq(v_fvarId_4937_, v_fvarId_4911_);
return v___x_4938_;
}
default: 
{
uint8_t v___x_4939_; 
v___x_4939_ = 0;
return v___x_4939_;
}
}
}
v___jp_4914_:
{
uint8_t v___x_4917_; 
v___x_4917_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4911_, v_d_4915_);
if (v___x_4917_ == 0)
{
v_e_4912_ = v_b_4916_;
goto _start;
}
else
{
return v___x_4913_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4940_, lean_object* v_e_4941_){
_start:
{
uint8_t v_res_4942_; lean_object* v_r_4943_; 
v_res_4942_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4940_, v_e_4941_);
lean_dec_ref(v_e_4941_);
lean_dec(v_fvarId_4940_);
v_r_4943_ = lean_box(v_res_4942_);
return v_r_4943_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4944_, lean_object* v_fvarId_4945_){
_start:
{
uint8_t v___x_4946_; 
v___x_4946_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4945_, v_e_4944_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4947_, lean_object* v_fvarId_4948_){
_start:
{
uint8_t v_res_4949_; lean_object* v_r_4950_; 
v_res_4949_ = l_Lean_Expr_containsFVar(v_e_4947_, v_fvarId_4948_);
lean_dec(v_fvarId_4948_);
lean_dec_ref(v_e_4947_);
v_r_4950_ = lean_box(v_res_4949_);
return v_r_4950_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(lean_object* v_p_4951_, lean_object* v_e_4952_){
_start:
{
uint8_t v___x_4953_; lean_object* v_d_4955_; lean_object* v_b_4956_; 
v___x_4953_ = l_Lean_Expr_hasExprMVar(v_e_4952_);
if (v___x_4953_ == 0)
{
lean_dec_ref(v_e_4952_);
lean_dec_ref(v_p_4951_);
return v___x_4953_;
}
else
{
switch(lean_obj_tag(v_e_4952_))
{
case 7:
{
lean_object* v_binderType_4959_; lean_object* v_body_4960_; 
v_binderType_4959_ = lean_ctor_get(v_e_4952_, 1);
lean_inc_ref(v_binderType_4959_);
v_body_4960_ = lean_ctor_get(v_e_4952_, 2);
lean_inc_ref(v_body_4960_);
lean_dec_ref_known(v_e_4952_, 3);
v_d_4955_ = v_binderType_4959_;
v_b_4956_ = v_body_4960_;
goto v___jp_4954_;
}
case 6:
{
lean_object* v_binderType_4961_; lean_object* v_body_4962_; 
v_binderType_4961_ = lean_ctor_get(v_e_4952_, 1);
lean_inc_ref(v_binderType_4961_);
v_body_4962_ = lean_ctor_get(v_e_4952_, 2);
lean_inc_ref(v_body_4962_);
lean_dec_ref_known(v_e_4952_, 3);
v_d_4955_ = v_binderType_4961_;
v_b_4956_ = v_body_4962_;
goto v___jp_4954_;
}
case 10:
{
lean_object* v_expr_4963_; 
v_expr_4963_ = lean_ctor_get(v_e_4952_, 1);
lean_inc_ref(v_expr_4963_);
lean_dec_ref_known(v_e_4952_, 2);
v_e_4952_ = v_expr_4963_;
goto _start;
}
case 8:
{
lean_object* v_type_4965_; lean_object* v_value_4966_; lean_object* v_body_4967_; uint8_t v___x_4968_; 
v_type_4965_ = lean_ctor_get(v_e_4952_, 1);
lean_inc_ref(v_type_4965_);
v_value_4966_ = lean_ctor_get(v_e_4952_, 2);
lean_inc_ref(v_value_4966_);
v_body_4967_ = lean_ctor_get(v_e_4952_, 3);
lean_inc_ref(v_body_4967_);
lean_dec_ref_known(v_e_4952_, 4);
lean_inc_ref(v_p_4951_);
v___x_4968_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4951_, v_type_4965_);
if (v___x_4968_ == 0)
{
uint8_t v___x_4969_; 
lean_inc_ref(v_p_4951_);
v___x_4969_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4951_, v_value_4966_);
if (v___x_4969_ == 0)
{
v_e_4952_ = v_body_4967_;
goto _start;
}
else
{
lean_dec_ref(v_body_4967_);
lean_dec_ref(v_p_4951_);
return v___x_4953_;
}
}
else
{
lean_dec_ref(v_body_4967_);
lean_dec_ref(v_value_4966_);
lean_dec_ref(v_p_4951_);
return v___x_4953_;
}
}
case 5:
{
lean_object* v_fn_4971_; lean_object* v_arg_4972_; uint8_t v___x_4973_; 
v_fn_4971_ = lean_ctor_get(v_e_4952_, 0);
lean_inc_ref(v_fn_4971_);
v_arg_4972_ = lean_ctor_get(v_e_4952_, 1);
lean_inc_ref(v_arg_4972_);
lean_dec_ref_known(v_e_4952_, 2);
lean_inc_ref(v_p_4951_);
v___x_4973_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4951_, v_fn_4971_);
if (v___x_4973_ == 0)
{
v_e_4952_ = v_arg_4972_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4972_);
lean_dec_ref(v_p_4951_);
return v___x_4953_;
}
}
case 11:
{
lean_object* v_struct_4975_; 
v_struct_4975_ = lean_ctor_get(v_e_4952_, 2);
lean_inc_ref(v_struct_4975_);
lean_dec_ref_known(v_e_4952_, 3);
v_e_4952_ = v_struct_4975_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_4977_; lean_object* v___x_4978_; uint8_t v___x_4979_; 
v_mvarId_4977_ = lean_ctor_get(v_e_4952_, 0);
lean_inc(v_mvarId_4977_);
lean_dec_ref_known(v_e_4952_, 1);
v___x_4978_ = lean_apply_1(v_p_4951_, v_mvarId_4977_);
v___x_4979_ = lean_unbox(v___x_4978_);
return v___x_4979_;
}
default: 
{
uint8_t v___x_4980_; 
lean_dec_ref(v_e_4952_);
lean_dec_ref(v_p_4951_);
v___x_4980_ = 0;
return v___x_4980_;
}
}
}
v___jp_4954_:
{
uint8_t v___x_4957_; 
lean_inc_ref(v_p_4951_);
v___x_4957_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4951_, v_d_4955_);
if (v___x_4957_ == 0)
{
v_e_4952_ = v_b_4956_;
goto _start;
}
else
{
lean_dec_ref(v_b_4956_);
lean_dec_ref(v_p_4951_);
return v___x_4953_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___boxed(lean_object* v_p_4981_, lean_object* v_e_4982_){
_start:
{
uint8_t v_res_4983_; lean_object* v_r_4984_; 
v_res_4983_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4981_, v_e_4982_);
v_r_4984_ = lean_box(v_res_4983_);
return v_r_4984_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyMVar(lean_object* v_e_4985_, lean_object* v_p_4986_){
_start:
{
uint8_t v___x_4987_; 
v___x_4987_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4986_, v_e_4985_);
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyMVar___boxed(lean_object* v_e_4988_, lean_object* v_p_4989_){
_start:
{
uint8_t v_res_4990_; lean_object* v_r_4991_; 
v_res_4990_ = l_Lean_Expr_hasAnyMVar(v_e_4988_, v_p_4989_);
v_r_4991_ = lean_box(v_res_4990_);
return v_r_4991_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(lean_object* v_mvarId_4992_, lean_object* v_e_4993_){
_start:
{
uint8_t v___x_4994_; lean_object* v_d_4996_; lean_object* v_b_4997_; 
v___x_4994_ = l_Lean_Expr_hasExprMVar(v_e_4993_);
if (v___x_4994_ == 0)
{
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
v_body_5001_ = lean_ctor_get(v_e_4993_, 2);
v_d_4996_ = v_binderType_5000_;
v_b_4997_ = v_body_5001_;
goto v___jp_4995_;
}
case 6:
{
lean_object* v_binderType_5002_; lean_object* v_body_5003_; 
v_binderType_5002_ = lean_ctor_get(v_e_4993_, 1);
v_body_5003_ = lean_ctor_get(v_e_4993_, 2);
v_d_4996_ = v_binderType_5002_;
v_b_4997_ = v_body_5003_;
goto v___jp_4995_;
}
case 10:
{
lean_object* v_expr_5004_; 
v_expr_5004_ = lean_ctor_get(v_e_4993_, 1);
v_e_4993_ = v_expr_5004_;
goto _start;
}
case 8:
{
lean_object* v_type_5006_; lean_object* v_value_5007_; lean_object* v_body_5008_; uint8_t v___x_5009_; 
v_type_5006_ = lean_ctor_get(v_e_4993_, 1);
v_value_5007_ = lean_ctor_get(v_e_4993_, 2);
v_body_5008_ = lean_ctor_get(v_e_4993_, 3);
v___x_5009_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4992_, v_type_5006_);
if (v___x_5009_ == 0)
{
uint8_t v___x_5010_; 
v___x_5010_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4992_, v_value_5007_);
if (v___x_5010_ == 0)
{
v_e_4993_ = v_body_5008_;
goto _start;
}
else
{
return v___x_4994_;
}
}
else
{
return v___x_4994_;
}
}
case 5:
{
lean_object* v_fn_5012_; lean_object* v_arg_5013_; uint8_t v___x_5014_; 
v_fn_5012_ = lean_ctor_get(v_e_4993_, 0);
v_arg_5013_ = lean_ctor_get(v_e_4993_, 1);
v___x_5014_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4992_, v_fn_5012_);
if (v___x_5014_ == 0)
{
v_e_4993_ = v_arg_5013_;
goto _start;
}
else
{
return v___x_4994_;
}
}
case 11:
{
lean_object* v_struct_5016_; 
v_struct_5016_ = lean_ctor_get(v_e_4993_, 2);
v_e_4993_ = v_struct_5016_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_5018_; uint8_t v___x_5019_; 
v_mvarId_5018_ = lean_ctor_get(v_e_4993_, 0);
v___x_5019_ = lean_name_eq(v_mvarId_5018_, v_mvarId_4992_);
return v___x_5019_;
}
default: 
{
uint8_t v___x_5020_; 
v___x_5020_ = 0;
return v___x_5020_;
}
}
}
v___jp_4995_:
{
uint8_t v___x_4998_; 
v___x_4998_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4992_, v_d_4996_);
if (v___x_4998_ == 0)
{
v_e_4993_ = v_b_4997_;
goto _start;
}
else
{
return v___x_4994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0___boxed(lean_object* v_mvarId_5021_, lean_object* v_e_5022_){
_start:
{
uint8_t v_res_5023_; lean_object* v_r_5024_; 
v_res_5023_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5021_, v_e_5022_);
lean_dec_ref(v_e_5022_);
lean_dec(v_mvarId_5021_);
v_r_5024_ = lean_box(v_res_5023_);
return v_r_5024_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsMVar(lean_object* v_e_5025_, lean_object* v_mvarId_5026_){
_start:
{
uint8_t v___x_5027_; 
v___x_5027_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5026_, v_e_5025_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsMVar___boxed(lean_object* v_e_5028_, lean_object* v_mvarId_5029_){
_start:
{
uint8_t v_res_5030_; lean_object* v_r_5031_; 
v_res_5030_ = l_Lean_Expr_containsMVar(v_e_5028_, v_mvarId_5029_);
lean_dec(v_mvarId_5029_);
lean_dec_ref(v_e_5028_);
v_r_5031_ = lean_box(v_res_5030_);
return v_r_5031_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5033_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_5034_ = lean_unsigned_to_nat(18u);
v___x_5035_ = lean_unsigned_to_nat(1906u);
v___x_5036_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_5037_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5038_ = l_mkPanicMessageWithDecl(v___x_5037_, v___x_5036_, v___x_5035_, v___x_5034_, v___x_5033_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_5039_, lean_object* v_newFn_5040_, lean_object* v_newArg_5041_){
_start:
{
if (lean_obj_tag(v_e_5039_) == 5)
{
lean_object* v_fn_5042_; lean_object* v_arg_5043_; size_t v___x_5044_; size_t v___x_5045_; uint8_t v___x_5046_; 
v_fn_5042_ = lean_ctor_get(v_e_5039_, 0);
v_arg_5043_ = lean_ctor_get(v_e_5039_, 1);
v___x_5044_ = lean_ptr_addr(v_fn_5042_);
v___x_5045_ = lean_ptr_addr(v_newFn_5040_);
v___x_5046_ = lean_usize_dec_eq(v___x_5044_, v___x_5045_);
if (v___x_5046_ == 0)
{
lean_object* v___x_5047_; 
v___x_5047_ = l_Lean_Expr_app___override(v_newFn_5040_, v_newArg_5041_);
return v___x_5047_;
}
else
{
size_t v___x_5048_; size_t v___x_5049_; uint8_t v___x_5050_; 
v___x_5048_ = lean_ptr_addr(v_arg_5043_);
v___x_5049_ = lean_ptr_addr(v_newArg_5041_);
v___x_5050_ = lean_usize_dec_eq(v___x_5048_, v___x_5049_);
if (v___x_5050_ == 0)
{
lean_object* v___x_5051_; 
v___x_5051_ = l_Lean_Expr_app___override(v_newFn_5040_, v_newArg_5041_);
return v___x_5051_;
}
else
{
lean_dec_ref(v_newArg_5041_);
lean_dec_ref(v_newFn_5040_);
lean_inc_ref(v_e_5039_);
return v_e_5039_;
}
}
}
else
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
lean_dec_ref(v_newArg_5041_);
lean_dec_ref(v_newFn_5040_);
v___x_5052_ = l_Lean_instInhabitedExpr;
v___x_5053_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_5054_ = l_panic___redArg(v___x_5052_, v___x_5053_);
return v___x_5054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_5055_, lean_object* v_newFn_5056_, lean_object* v_newArg_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_5055_, v_newFn_5056_, v_newArg_5057_);
lean_dec_ref(v_e_5055_);
return v_res_5058_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5060_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_5061_ = lean_unsigned_to_nat(20u);
v___x_5062_ = lean_unsigned_to_nat(1917u);
v___x_5063_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_5064_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5065_ = l_mkPanicMessageWithDecl(v___x_5064_, v___x_5063_, v___x_5062_, v___x_5061_, v___x_5060_);
return v___x_5065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_5066_, lean_object* v_fvarIdNew_5067_){
_start:
{
if (lean_obj_tag(v_e_5066_) == 1)
{
lean_object* v_fvarId_5068_; uint8_t v___x_5069_; 
v_fvarId_5068_ = lean_ctor_get(v_e_5066_, 0);
v___x_5069_ = lean_name_eq(v_fvarId_5068_, v_fvarIdNew_5067_);
if (v___x_5069_ == 0)
{
lean_object* v___x_5070_; 
v___x_5070_ = l_Lean_Expr_fvar___override(v_fvarIdNew_5067_);
return v___x_5070_;
}
else
{
lean_dec(v_fvarIdNew_5067_);
lean_inc_ref(v_e_5066_);
return v_e_5066_;
}
}
else
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
lean_dec(v_fvarIdNew_5067_);
v___x_5071_ = l_Lean_instInhabitedExpr;
v___x_5072_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_5073_ = l_panic___redArg(v___x_5071_, v___x_5072_);
return v___x_5073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_5074_, lean_object* v_fvarIdNew_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_Lean_Expr_updateFVar_x21(v_e_5074_, v_fvarIdNew_5075_);
lean_dec_ref(v_e_5074_);
return v_res_5076_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5078_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_5079_ = lean_unsigned_to_nat(18u);
v___x_5080_ = lean_unsigned_to_nat(1922u);
v___x_5081_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_5082_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5083_ = l_mkPanicMessageWithDecl(v___x_5082_, v___x_5081_, v___x_5080_, v___x_5079_, v___x_5078_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_5084_, lean_object* v_newLevels_5085_){
_start:
{
if (lean_obj_tag(v_e_5084_) == 4)
{
lean_object* v_declName_5086_; lean_object* v_us_5087_; uint8_t v___x_5088_; 
v_declName_5086_ = lean_ctor_get(v_e_5084_, 0);
v_us_5087_ = lean_ctor_get(v_e_5084_, 1);
v___x_5088_ = l_ptrEqList___redArg(v_us_5087_, v_newLevels_5085_);
if (v___x_5088_ == 0)
{
lean_object* v___x_5089_; 
lean_inc(v_declName_5086_);
lean_dec_ref_known(v_e_5084_, 2);
v___x_5089_ = l_Lean_Expr_const___override(v_declName_5086_, v_newLevels_5085_);
return v___x_5089_;
}
else
{
lean_dec(v_newLevels_5085_);
return v_e_5084_;
}
}
else
{
lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; 
lean_dec(v_newLevels_5085_);
lean_dec_ref(v_e_5084_);
v___x_5090_ = l_Lean_instInhabitedExpr;
v___x_5091_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_5092_ = l_panic___redArg(v___x_5090_, v___x_5091_);
return v___x_5092_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5095_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_5096_ = lean_unsigned_to_nat(14u);
v___x_5097_ = lean_unsigned_to_nat(1933u);
v___x_5098_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_5099_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5100_ = l_mkPanicMessageWithDecl(v___x_5099_, v___x_5098_, v___x_5097_, v___x_5096_, v___x_5095_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_5101_, lean_object* v_u_x27_5102_){
_start:
{
if (lean_obj_tag(v_e_5101_) == 3)
{
lean_object* v_u_5103_; size_t v___x_5104_; size_t v___x_5105_; uint8_t v___x_5106_; 
v_u_5103_ = lean_ctor_get(v_e_5101_, 0);
v___x_5104_ = lean_ptr_addr(v_u_5103_);
v___x_5105_ = lean_ptr_addr(v_u_x27_5102_);
v___x_5106_ = lean_usize_dec_eq(v___x_5104_, v___x_5105_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5107_; 
v___x_5107_ = l_Lean_Expr_sort___override(v_u_x27_5102_);
return v___x_5107_;
}
else
{
lean_dec(v_u_x27_5102_);
lean_inc_ref(v_e_5101_);
return v_e_5101_;
}
}
else
{
lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; 
lean_dec(v_u_x27_5102_);
v___x_5108_ = l_Lean_instInhabitedExpr;
v___x_5109_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5110_ = l_panic___redArg(v___x_5108_, v___x_5109_);
return v___x_5110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5111_, lean_object* v_u_x27_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5111_, v_u_x27_5112_);
lean_dec_ref(v_e_5111_);
return v_res_5113_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; 
v___x_5116_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5117_ = lean_unsigned_to_nat(17u);
v___x_5118_ = lean_unsigned_to_nat(1944u);
v___x_5119_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5120_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5121_ = l_mkPanicMessageWithDecl(v___x_5120_, v___x_5119_, v___x_5118_, v___x_5117_, v___x_5116_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5122_, lean_object* v_newExpr_5123_){
_start:
{
if (lean_obj_tag(v_e_5122_) == 10)
{
lean_object* v_data_5124_; lean_object* v_expr_5125_; size_t v___x_5126_; size_t v___x_5127_; uint8_t v___x_5128_; 
v_data_5124_ = lean_ctor_get(v_e_5122_, 0);
v_expr_5125_ = lean_ctor_get(v_e_5122_, 1);
v___x_5126_ = lean_ptr_addr(v_expr_5125_);
v___x_5127_ = lean_ptr_addr(v_newExpr_5123_);
v___x_5128_ = lean_usize_dec_eq(v___x_5126_, v___x_5127_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; 
lean_inc(v_data_5124_);
lean_dec_ref_known(v_e_5122_, 2);
v___x_5129_ = l_Lean_Expr_mdata___override(v_data_5124_, v_newExpr_5123_);
return v___x_5129_;
}
else
{
lean_dec_ref(v_newExpr_5123_);
return v_e_5122_;
}
}
else
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; 
lean_dec_ref(v_newExpr_5123_);
lean_dec_ref(v_e_5122_);
v___x_5130_ = l_Lean_instInhabitedExpr;
v___x_5131_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5132_ = l_panic___redArg(v___x_5130_, v___x_5131_);
return v___x_5132_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5135_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5136_ = lean_unsigned_to_nat(18u);
v___x_5137_ = lean_unsigned_to_nat(1955u);
v___x_5138_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5139_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5140_ = l_mkPanicMessageWithDecl(v___x_5139_, v___x_5138_, v___x_5137_, v___x_5136_, v___x_5135_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5141_, lean_object* v_newExpr_5142_){
_start:
{
if (lean_obj_tag(v_e_5141_) == 11)
{
lean_object* v_typeName_5143_; lean_object* v_idx_5144_; lean_object* v_struct_5145_; size_t v___x_5146_; size_t v___x_5147_; uint8_t v___x_5148_; 
v_typeName_5143_ = lean_ctor_get(v_e_5141_, 0);
v_idx_5144_ = lean_ctor_get(v_e_5141_, 1);
v_struct_5145_ = lean_ctor_get(v_e_5141_, 2);
v___x_5146_ = lean_ptr_addr(v_struct_5145_);
v___x_5147_ = lean_ptr_addr(v_newExpr_5142_);
v___x_5148_ = lean_usize_dec_eq(v___x_5146_, v___x_5147_);
if (v___x_5148_ == 0)
{
lean_object* v___x_5149_; 
lean_inc(v_idx_5144_);
lean_inc(v_typeName_5143_);
lean_dec_ref_known(v_e_5141_, 3);
v___x_5149_ = l_Lean_Expr_proj___override(v_typeName_5143_, v_idx_5144_, v_newExpr_5142_);
return v___x_5149_;
}
else
{
lean_dec_ref(v_newExpr_5142_);
return v_e_5141_;
}
}
else
{
lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
lean_dec_ref(v_newExpr_5142_);
lean_dec_ref(v_e_5141_);
v___x_5150_ = l_Lean_instInhabitedExpr;
v___x_5151_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5152_ = l_panic___redArg(v___x_5150_, v___x_5151_);
return v___x_5152_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; 
v___x_5155_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5156_ = lean_unsigned_to_nat(23u);
v___x_5157_ = lean_unsigned_to_nat(1970u);
v___x_5158_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5159_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5160_ = l_mkPanicMessageWithDecl(v___x_5159_, v___x_5158_, v___x_5157_, v___x_5156_, v___x_5155_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5161_, uint8_t v_newBinfo_5162_, lean_object* v_newDomain_5163_, lean_object* v_newBody_5164_){
_start:
{
if (lean_obj_tag(v_e_5161_) == 7)
{
lean_object* v_binderName_5165_; lean_object* v_binderType_5166_; lean_object* v_body_5167_; uint8_t v_binderInfo_5168_; size_t v___x_5169_; size_t v___x_5170_; uint8_t v___x_5171_; 
v_binderName_5165_ = lean_ctor_get(v_e_5161_, 0);
v_binderType_5166_ = lean_ctor_get(v_e_5161_, 1);
v_body_5167_ = lean_ctor_get(v_e_5161_, 2);
v_binderInfo_5168_ = lean_ctor_get_uint8(v_e_5161_, sizeof(void*)*3 + 8);
v___x_5169_ = lean_ptr_addr(v_binderType_5166_);
v___x_5170_ = lean_ptr_addr(v_newDomain_5163_);
v___x_5171_ = lean_usize_dec_eq(v___x_5169_, v___x_5170_);
if (v___x_5171_ == 0)
{
lean_object* v___x_5172_; 
lean_inc(v_binderName_5165_);
lean_dec_ref_known(v_e_5161_, 3);
v___x_5172_ = l_Lean_Expr_forallE___override(v_binderName_5165_, v_newDomain_5163_, v_newBody_5164_, v_newBinfo_5162_);
return v___x_5172_;
}
else
{
size_t v___x_5173_; size_t v___x_5174_; uint8_t v___x_5175_; 
v___x_5173_ = lean_ptr_addr(v_body_5167_);
v___x_5174_ = lean_ptr_addr(v_newBody_5164_);
v___x_5175_ = lean_usize_dec_eq(v___x_5173_, v___x_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; 
lean_inc(v_binderName_5165_);
lean_dec_ref_known(v_e_5161_, 3);
v___x_5176_ = l_Lean_Expr_forallE___override(v_binderName_5165_, v_newDomain_5163_, v_newBody_5164_, v_newBinfo_5162_);
return v___x_5176_;
}
else
{
uint8_t v___x_5177_; 
v___x_5177_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5168_, v_newBinfo_5162_);
if (v___x_5177_ == 0)
{
lean_object* v___x_5178_; 
lean_inc(v_binderName_5165_);
lean_dec_ref_known(v_e_5161_, 3);
v___x_5178_ = l_Lean_Expr_forallE___override(v_binderName_5165_, v_newDomain_5163_, v_newBody_5164_, v_newBinfo_5162_);
return v___x_5178_;
}
else
{
lean_dec_ref(v_newBody_5164_);
lean_dec_ref(v_newDomain_5163_);
return v_e_5161_;
}
}
}
}
else
{
lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
lean_dec_ref(v_newBody_5164_);
lean_dec_ref(v_newDomain_5163_);
lean_dec_ref(v_e_5161_);
v___x_5179_ = l_Lean_instInhabitedExpr;
v___x_5180_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5181_ = l_panic___redArg(v___x_5179_, v___x_5180_);
return v___x_5181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5182_, lean_object* v_newBinfo_5183_, lean_object* v_newDomain_5184_, lean_object* v_newBody_5185_){
_start:
{
uint8_t v_newBinfo_boxed_5186_; lean_object* v_res_5187_; 
v_newBinfo_boxed_5186_ = lean_unbox(v_newBinfo_5183_);
v_res_5187_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5182_, v_newBinfo_boxed_5186_, v_newDomain_5184_, v_newBody_5185_);
return v_res_5187_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
v___x_5189_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5190_ = lean_unsigned_to_nat(24u);
v___x_5191_ = lean_unsigned_to_nat(1981u);
v___x_5192_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5193_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5194_ = l_mkPanicMessageWithDecl(v___x_5193_, v___x_5192_, v___x_5191_, v___x_5190_, v___x_5189_);
return v___x_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5195_, lean_object* v_newDomain_5196_, lean_object* v_newBody_5197_){
_start:
{
if (lean_obj_tag(v_e_5195_) == 7)
{
lean_object* v_binderName_5198_; lean_object* v_binderType_5199_; lean_object* v_body_5200_; uint8_t v_binderInfo_5201_; size_t v___x_5202_; size_t v___x_5203_; uint8_t v___x_5204_; 
v_binderName_5198_ = lean_ctor_get(v_e_5195_, 0);
v_binderType_5199_ = lean_ctor_get(v_e_5195_, 1);
v_body_5200_ = lean_ctor_get(v_e_5195_, 2);
v_binderInfo_5201_ = lean_ctor_get_uint8(v_e_5195_, sizeof(void*)*3 + 8);
v___x_5202_ = lean_ptr_addr(v_binderType_5199_);
v___x_5203_ = lean_ptr_addr(v_newDomain_5196_);
v___x_5204_ = lean_usize_dec_eq(v___x_5202_, v___x_5203_);
if (v___x_5204_ == 0)
{
lean_object* v___x_5205_; 
lean_inc(v_binderName_5198_);
lean_dec_ref_known(v_e_5195_, 3);
v___x_5205_ = l_Lean_Expr_forallE___override(v_binderName_5198_, v_newDomain_5196_, v_newBody_5197_, v_binderInfo_5201_);
return v___x_5205_;
}
else
{
size_t v___x_5206_; size_t v___x_5207_; uint8_t v___x_5208_; 
v___x_5206_ = lean_ptr_addr(v_body_5200_);
v___x_5207_ = lean_ptr_addr(v_newBody_5197_);
v___x_5208_ = lean_usize_dec_eq(v___x_5206_, v___x_5207_);
if (v___x_5208_ == 0)
{
lean_object* v___x_5209_; 
lean_inc(v_binderName_5198_);
lean_dec_ref_known(v_e_5195_, 3);
v___x_5209_ = l_Lean_Expr_forallE___override(v_binderName_5198_, v_newDomain_5196_, v_newBody_5197_, v_binderInfo_5201_);
return v___x_5209_;
}
else
{
uint8_t v___x_5210_; 
v___x_5210_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5201_, v_binderInfo_5201_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; 
lean_inc(v_binderName_5198_);
lean_dec_ref_known(v_e_5195_, 3);
v___x_5211_ = l_Lean_Expr_forallE___override(v_binderName_5198_, v_newDomain_5196_, v_newBody_5197_, v_binderInfo_5201_);
return v___x_5211_;
}
else
{
lean_dec_ref(v_newBody_5197_);
lean_dec_ref(v_newDomain_5196_);
return v_e_5195_;
}
}
}
}
else
{
lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; 
lean_dec_ref(v_newBody_5197_);
lean_dec_ref(v_newDomain_5196_);
lean_dec_ref(v_e_5195_);
v___x_5212_ = l_Lean_instInhabitedExpr;
v___x_5213_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5214_ = l_panic___redArg(v___x_5212_, v___x_5213_);
return v___x_5214_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; 
v___x_5217_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5218_ = lean_unsigned_to_nat(19u);
v___x_5219_ = lean_unsigned_to_nat(1990u);
v___x_5220_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5221_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5222_ = l_mkPanicMessageWithDecl(v___x_5221_, v___x_5220_, v___x_5219_, v___x_5218_, v___x_5217_);
return v___x_5222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5223_, uint8_t v_newBinfo_5224_, lean_object* v_newDomain_5225_, lean_object* v_newBody_5226_){
_start:
{
if (lean_obj_tag(v_e_5223_) == 6)
{
lean_object* v_binderName_5227_; lean_object* v_binderType_5228_; lean_object* v_body_5229_; uint8_t v_binderInfo_5230_; size_t v___x_5231_; size_t v___x_5232_; uint8_t v___x_5233_; 
v_binderName_5227_ = lean_ctor_get(v_e_5223_, 0);
v_binderType_5228_ = lean_ctor_get(v_e_5223_, 1);
v_body_5229_ = lean_ctor_get(v_e_5223_, 2);
v_binderInfo_5230_ = lean_ctor_get_uint8(v_e_5223_, sizeof(void*)*3 + 8);
v___x_5231_ = lean_ptr_addr(v_binderType_5228_);
v___x_5232_ = lean_ptr_addr(v_newDomain_5225_);
v___x_5233_ = lean_usize_dec_eq(v___x_5231_, v___x_5232_);
if (v___x_5233_ == 0)
{
lean_object* v___x_5234_; 
lean_inc(v_binderName_5227_);
lean_dec_ref_known(v_e_5223_, 3);
v___x_5234_ = l_Lean_Expr_lam___override(v_binderName_5227_, v_newDomain_5225_, v_newBody_5226_, v_newBinfo_5224_);
return v___x_5234_;
}
else
{
size_t v___x_5235_; size_t v___x_5236_; uint8_t v___x_5237_; 
v___x_5235_ = lean_ptr_addr(v_body_5229_);
v___x_5236_ = lean_ptr_addr(v_newBody_5226_);
v___x_5237_ = lean_usize_dec_eq(v___x_5235_, v___x_5236_);
if (v___x_5237_ == 0)
{
lean_object* v___x_5238_; 
lean_inc(v_binderName_5227_);
lean_dec_ref_known(v_e_5223_, 3);
v___x_5238_ = l_Lean_Expr_lam___override(v_binderName_5227_, v_newDomain_5225_, v_newBody_5226_, v_newBinfo_5224_);
return v___x_5238_;
}
else
{
uint8_t v___x_5239_; 
v___x_5239_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5230_, v_newBinfo_5224_);
if (v___x_5239_ == 0)
{
lean_object* v___x_5240_; 
lean_inc(v_binderName_5227_);
lean_dec_ref_known(v_e_5223_, 3);
v___x_5240_ = l_Lean_Expr_lam___override(v_binderName_5227_, v_newDomain_5225_, v_newBody_5226_, v_newBinfo_5224_);
return v___x_5240_;
}
else
{
lean_dec_ref(v_newBody_5226_);
lean_dec_ref(v_newDomain_5225_);
return v_e_5223_;
}
}
}
}
else
{
lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; 
lean_dec_ref(v_newBody_5226_);
lean_dec_ref(v_newDomain_5225_);
lean_dec_ref(v_e_5223_);
v___x_5241_ = l_Lean_instInhabitedExpr;
v___x_5242_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5243_ = l_panic___redArg(v___x_5241_, v___x_5242_);
return v___x_5243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5244_, lean_object* v_newBinfo_5245_, lean_object* v_newDomain_5246_, lean_object* v_newBody_5247_){
_start:
{
uint8_t v_newBinfo_boxed_5248_; lean_object* v_res_5249_; 
v_newBinfo_boxed_5248_ = lean_unbox(v_newBinfo_5245_);
v_res_5249_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5244_, v_newBinfo_boxed_5248_, v_newDomain_5246_, v_newBody_5247_);
return v_res_5249_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; 
v___x_5251_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5252_ = lean_unsigned_to_nat(20u);
v___x_5253_ = lean_unsigned_to_nat(2001u);
v___x_5254_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5255_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5256_ = l_mkPanicMessageWithDecl(v___x_5255_, v___x_5254_, v___x_5253_, v___x_5252_, v___x_5251_);
return v___x_5256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5257_, lean_object* v_newDomain_5258_, lean_object* v_newBody_5259_){
_start:
{
if (lean_obj_tag(v_e_5257_) == 6)
{
lean_object* v_binderName_5260_; lean_object* v_binderType_5261_; lean_object* v_body_5262_; uint8_t v_binderInfo_5263_; size_t v___x_5264_; size_t v___x_5265_; uint8_t v___x_5266_; 
v_binderName_5260_ = lean_ctor_get(v_e_5257_, 0);
v_binderType_5261_ = lean_ctor_get(v_e_5257_, 1);
v_body_5262_ = lean_ctor_get(v_e_5257_, 2);
v_binderInfo_5263_ = lean_ctor_get_uint8(v_e_5257_, sizeof(void*)*3 + 8);
v___x_5264_ = lean_ptr_addr(v_binderType_5261_);
v___x_5265_ = lean_ptr_addr(v_newDomain_5258_);
v___x_5266_ = lean_usize_dec_eq(v___x_5264_, v___x_5265_);
if (v___x_5266_ == 0)
{
lean_object* v___x_5267_; 
lean_inc(v_binderName_5260_);
lean_dec_ref_known(v_e_5257_, 3);
v___x_5267_ = l_Lean_Expr_lam___override(v_binderName_5260_, v_newDomain_5258_, v_newBody_5259_, v_binderInfo_5263_);
return v___x_5267_;
}
else
{
size_t v___x_5268_; size_t v___x_5269_; uint8_t v___x_5270_; 
v___x_5268_ = lean_ptr_addr(v_body_5262_);
v___x_5269_ = lean_ptr_addr(v_newBody_5259_);
v___x_5270_ = lean_usize_dec_eq(v___x_5268_, v___x_5269_);
if (v___x_5270_ == 0)
{
lean_object* v___x_5271_; 
lean_inc(v_binderName_5260_);
lean_dec_ref_known(v_e_5257_, 3);
v___x_5271_ = l_Lean_Expr_lam___override(v_binderName_5260_, v_newDomain_5258_, v_newBody_5259_, v_binderInfo_5263_);
return v___x_5271_;
}
else
{
uint8_t v___x_5272_; 
v___x_5272_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5263_, v_binderInfo_5263_);
if (v___x_5272_ == 0)
{
lean_object* v___x_5273_; 
lean_inc(v_binderName_5260_);
lean_dec_ref_known(v_e_5257_, 3);
v___x_5273_ = l_Lean_Expr_lam___override(v_binderName_5260_, v_newDomain_5258_, v_newBody_5259_, v_binderInfo_5263_);
return v___x_5273_;
}
else
{
lean_dec_ref(v_newBody_5259_);
lean_dec_ref(v_newDomain_5258_);
return v_e_5257_;
}
}
}
}
else
{
lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; 
lean_dec_ref(v_newBody_5259_);
lean_dec_ref(v_newDomain_5258_);
lean_dec_ref(v_e_5257_);
v___x_5274_ = l_Lean_instInhabitedExpr;
v___x_5275_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5276_ = l_panic___redArg(v___x_5274_, v___x_5275_);
return v___x_5276_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___x_5278_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5279_ = lean_unsigned_to_nat(22u);
v___x_5280_ = lean_unsigned_to_nat(2010u);
v___x_5281_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5282_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5283_ = l_mkPanicMessageWithDecl(v___x_5282_, v___x_5281_, v___x_5280_, v___x_5279_, v___x_5278_);
return v___x_5283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5284_, lean_object* v_newType_5285_, lean_object* v_newVal_5286_, lean_object* v_newBody_5287_, uint8_t v_newNondep_5288_){
_start:
{
if (lean_obj_tag(v_e_5284_) == 8)
{
lean_object* v_declName_5289_; lean_object* v_type_5290_; lean_object* v_value_5291_; lean_object* v_body_5292_; uint8_t v_nondep_5293_; size_t v___x_5294_; size_t v___x_5295_; uint8_t v___x_5296_; 
v_declName_5289_ = lean_ctor_get(v_e_5284_, 0);
v_type_5290_ = lean_ctor_get(v_e_5284_, 1);
v_value_5291_ = lean_ctor_get(v_e_5284_, 2);
v_body_5292_ = lean_ctor_get(v_e_5284_, 3);
v_nondep_5293_ = lean_ctor_get_uint8(v_e_5284_, sizeof(void*)*4 + 8);
v___x_5294_ = lean_ptr_addr(v_type_5290_);
v___x_5295_ = lean_ptr_addr(v_newType_5285_);
v___x_5296_ = lean_usize_dec_eq(v___x_5294_, v___x_5295_);
if (v___x_5296_ == 0)
{
lean_object* v___x_5297_; 
lean_inc(v_declName_5289_);
lean_dec_ref_known(v_e_5284_, 4);
v___x_5297_ = l_Lean_Expr_letE___override(v_declName_5289_, v_newType_5285_, v_newVal_5286_, v_newBody_5287_, v_newNondep_5288_);
return v___x_5297_;
}
else
{
size_t v___x_5298_; size_t v___x_5299_; uint8_t v___x_5300_; 
v___x_5298_ = lean_ptr_addr(v_value_5291_);
v___x_5299_ = lean_ptr_addr(v_newVal_5286_);
v___x_5300_ = lean_usize_dec_eq(v___x_5298_, v___x_5299_);
if (v___x_5300_ == 0)
{
lean_object* v___x_5301_; 
lean_inc(v_declName_5289_);
lean_dec_ref_known(v_e_5284_, 4);
v___x_5301_ = l_Lean_Expr_letE___override(v_declName_5289_, v_newType_5285_, v_newVal_5286_, v_newBody_5287_, v_newNondep_5288_);
return v___x_5301_;
}
else
{
size_t v___x_5302_; size_t v___x_5303_; uint8_t v___x_5304_; 
v___x_5302_ = lean_ptr_addr(v_body_5292_);
v___x_5303_ = lean_ptr_addr(v_newBody_5287_);
v___x_5304_ = lean_usize_dec_eq(v___x_5302_, v___x_5303_);
if (v___x_5304_ == 0)
{
lean_object* v___x_5305_; 
lean_inc(v_declName_5289_);
lean_dec_ref_known(v_e_5284_, 4);
v___x_5305_ = l_Lean_Expr_letE___override(v_declName_5289_, v_newType_5285_, v_newVal_5286_, v_newBody_5287_, v_newNondep_5288_);
return v___x_5305_;
}
else
{
if (v_newNondep_5288_ == 0)
{
if (v_nondep_5293_ == 0)
{
lean_dec_ref(v_newBody_5287_);
lean_dec_ref(v_newVal_5286_);
lean_dec_ref(v_newType_5285_);
return v_e_5284_;
}
else
{
lean_object* v___x_5306_; 
lean_inc(v_declName_5289_);
lean_dec_ref_known(v_e_5284_, 4);
v___x_5306_ = l_Lean_Expr_letE___override(v_declName_5289_, v_newType_5285_, v_newVal_5286_, v_newBody_5287_, v_newNondep_5288_);
return v___x_5306_;
}
}
else
{
if (v_nondep_5293_ == 0)
{
lean_object* v___x_5307_; 
lean_inc(v_declName_5289_);
lean_dec_ref_known(v_e_5284_, 4);
v___x_5307_ = l_Lean_Expr_letE___override(v_declName_5289_, v_newType_5285_, v_newVal_5286_, v_newBody_5287_, v_newNondep_5288_);
return v___x_5307_;
}
else
{
lean_dec_ref(v_newBody_5287_);
lean_dec_ref(v_newVal_5286_);
lean_dec_ref(v_newType_5285_);
return v_e_5284_;
}
}
}
}
}
}
else
{
lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; 
lean_dec_ref(v_newBody_5287_);
lean_dec_ref(v_newVal_5286_);
lean_dec_ref(v_newType_5285_);
lean_dec_ref(v_e_5284_);
v___x_5308_ = l_Lean_instInhabitedExpr;
v___x_5309_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5310_ = l_panic___redArg(v___x_5308_, v___x_5309_);
return v___x_5310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5311_, lean_object* v_newType_5312_, lean_object* v_newVal_5313_, lean_object* v_newBody_5314_, lean_object* v_newNondep_5315_){
_start:
{
uint8_t v_newNondep_boxed_5316_; lean_object* v_res_5317_; 
v_newNondep_boxed_5316_ = lean_unbox(v_newNondep_5315_);
v_res_5317_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5311_, v_newType_5312_, v_newVal_5313_, v_newBody_5314_, v_newNondep_boxed_5316_);
return v_res_5317_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; 
v___x_5319_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5320_ = lean_unsigned_to_nat(27u);
v___x_5321_ = lean_unsigned_to_nat(2023u);
v___x_5322_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5323_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5324_ = l_mkPanicMessageWithDecl(v___x_5323_, v___x_5322_, v___x_5321_, v___x_5320_, v___x_5319_);
return v___x_5324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5325_, lean_object* v_newType_5326_, lean_object* v_newVal_5327_, lean_object* v_newBody_5328_){
_start:
{
if (lean_obj_tag(v_e_5325_) == 8)
{
lean_object* v_declName_5329_; lean_object* v_type_5330_; lean_object* v_value_5331_; lean_object* v_body_5332_; uint8_t v_nondep_5333_; size_t v___x_5334_; size_t v___x_5335_; uint8_t v___x_5336_; 
v_declName_5329_ = lean_ctor_get(v_e_5325_, 0);
v_type_5330_ = lean_ctor_get(v_e_5325_, 1);
v_value_5331_ = lean_ctor_get(v_e_5325_, 2);
v_body_5332_ = lean_ctor_get(v_e_5325_, 3);
v_nondep_5333_ = lean_ctor_get_uint8(v_e_5325_, sizeof(void*)*4 + 8);
v___x_5334_ = lean_ptr_addr(v_type_5330_);
v___x_5335_ = lean_ptr_addr(v_newType_5326_);
v___x_5336_ = lean_usize_dec_eq(v___x_5334_, v___x_5335_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5337_; 
lean_inc(v_declName_5329_);
lean_dec_ref_known(v_e_5325_, 4);
v___x_5337_ = l_Lean_Expr_letE___override(v_declName_5329_, v_newType_5326_, v_newVal_5327_, v_newBody_5328_, v_nondep_5333_);
return v___x_5337_;
}
else
{
size_t v___x_5338_; size_t v___x_5339_; uint8_t v___x_5340_; 
v___x_5338_ = lean_ptr_addr(v_value_5331_);
v___x_5339_ = lean_ptr_addr(v_newVal_5327_);
v___x_5340_ = lean_usize_dec_eq(v___x_5338_, v___x_5339_);
if (v___x_5340_ == 0)
{
lean_object* v___x_5341_; 
lean_inc(v_declName_5329_);
lean_dec_ref_known(v_e_5325_, 4);
v___x_5341_ = l_Lean_Expr_letE___override(v_declName_5329_, v_newType_5326_, v_newVal_5327_, v_newBody_5328_, v_nondep_5333_);
return v___x_5341_;
}
else
{
size_t v___x_5342_; size_t v___x_5343_; uint8_t v___x_5344_; 
v___x_5342_ = lean_ptr_addr(v_body_5332_);
v___x_5343_ = lean_ptr_addr(v_newBody_5328_);
v___x_5344_ = lean_usize_dec_eq(v___x_5342_, v___x_5343_);
if (v___x_5344_ == 0)
{
lean_object* v___x_5345_; 
lean_inc(v_declName_5329_);
lean_dec_ref_known(v_e_5325_, 4);
v___x_5345_ = l_Lean_Expr_letE___override(v_declName_5329_, v_newType_5326_, v_newVal_5327_, v_newBody_5328_, v_nondep_5333_);
return v___x_5345_;
}
else
{
lean_dec_ref(v_newBody_5328_);
lean_dec_ref(v_newVal_5327_);
lean_dec_ref(v_newType_5326_);
return v_e_5325_;
}
}
}
}
else
{
lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; 
lean_dec_ref(v_newBody_5328_);
lean_dec_ref(v_newVal_5327_);
lean_dec_ref(v_newType_5326_);
lean_dec_ref(v_e_5325_);
v___x_5346_ = l_Lean_instInhabitedExpr;
v___x_5347_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5348_ = l_panic___redArg(v___x_5346_, v___x_5347_);
return v___x_5348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5349_, lean_object* v_x_5350_){
_start:
{
if (lean_obj_tag(v_x_5349_) == 5)
{
lean_object* v_fn_5351_; lean_object* v_arg_5352_; lean_object* v___x_5353_; size_t v___x_5354_; size_t v___x_5355_; uint8_t v___x_5356_; 
v_fn_5351_ = lean_ctor_get(v_x_5349_, 0);
v_arg_5352_ = lean_ctor_get(v_x_5349_, 1);
lean_inc_ref(v_fn_5351_);
v___x_5353_ = l_Lean_Expr_updateFn(v_fn_5351_, v_x_5350_);
v___x_5354_ = lean_ptr_addr(v_fn_5351_);
v___x_5355_ = lean_ptr_addr(v___x_5353_);
v___x_5356_ = lean_usize_dec_eq(v___x_5354_, v___x_5355_);
if (v___x_5356_ == 0)
{
lean_object* v___x_5357_; 
lean_inc_ref(v_arg_5352_);
lean_dec_ref_known(v_x_5349_, 2);
v___x_5357_ = l_Lean_Expr_app___override(v___x_5353_, v_arg_5352_);
return v___x_5357_;
}
else
{
size_t v___x_5358_; size_t v___x_5359_; uint8_t v___x_5360_; 
v___x_5358_ = lean_ptr_addr(v_arg_5352_);
v___x_5359_ = lean_ptr_addr(v_arg_5352_);
v___x_5360_ = lean_usize_dec_eq(v___x_5358_, v___x_5359_);
if (v___x_5360_ == 0)
{
lean_object* v___x_5361_; 
lean_inc_ref(v_arg_5352_);
lean_dec_ref_known(v_x_5349_, 2);
v___x_5361_ = l_Lean_Expr_app___override(v___x_5353_, v_arg_5352_);
return v___x_5361_;
}
else
{
lean_dec_ref(v___x_5353_);
return v_x_5349_;
}
}
}
else
{
lean_dec_ref(v_x_5349_);
lean_inc_ref(v_x_5350_);
return v_x_5350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5362_, lean_object* v_x_5363_){
_start:
{
lean_object* v_res_5364_; 
v_res_5364_ = l_Lean_Expr_updateFn(v_x_5362_, v_x_5363_);
lean_dec_ref(v_x_5363_);
return v_res_5364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5365_){
_start:
{
if (lean_obj_tag(v_e_5365_) == 6)
{
lean_object* v_binderName_5366_; lean_object* v_binderType_5367_; lean_object* v_body_5368_; uint8_t v_binderInfo_5369_; lean_object* v_b_x27_5370_; 
v_binderName_5366_ = lean_ctor_get(v_e_5365_, 0);
v_binderType_5367_ = lean_ctor_get(v_e_5365_, 1);
v_body_5368_ = lean_ctor_get(v_e_5365_, 2);
v_binderInfo_5369_ = lean_ctor_get_uint8(v_e_5365_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5368_);
v_b_x27_5370_ = l_Lean_Expr_eta(v_body_5368_);
if (lean_obj_tag(v_b_x27_5370_) == 5)
{
lean_object* v_arg_5382_; 
v_arg_5382_ = lean_ctor_get(v_b_x27_5370_, 1);
if (lean_obj_tag(v_arg_5382_) == 0)
{
lean_object* v_fn_5383_; lean_object* v_deBruijnIndex_5384_; lean_object* v___x_5385_; uint8_t v___x_5386_; 
v_fn_5383_ = lean_ctor_get(v_b_x27_5370_, 0);
v_deBruijnIndex_5384_ = lean_ctor_get(v_arg_5382_, 0);
v___x_5385_ = lean_unsigned_to_nat(0u);
v___x_5386_ = lean_nat_dec_eq(v_deBruijnIndex_5384_, v___x_5385_);
if (v___x_5386_ == 0)
{
goto v___jp_5371_;
}
else
{
uint8_t v___x_5387_; 
v___x_5387_ = lean_expr_has_loose_bvar(v_fn_5383_, v___x_5385_);
if (v___x_5387_ == 0)
{
lean_object* v___x_5388_; lean_object* v___x_5389_; 
lean_inc_ref(v_fn_5383_);
lean_dec_ref_known(v_b_x27_5370_, 2);
lean_dec_ref_known(v_e_5365_, 3);
v___x_5388_ = lean_unsigned_to_nat(1u);
v___x_5389_ = lean_expr_lower_loose_bvars(v_fn_5383_, v___x_5388_, v___x_5388_);
lean_dec_ref(v_fn_5383_);
return v___x_5389_;
}
else
{
size_t v___x_5390_; size_t v___x_5391_; uint8_t v___x_5392_; 
v___x_5390_ = lean_ptr_addr(v_binderType_5367_);
v___x_5391_ = lean_ptr_addr(v_binderType_5367_);
v___x_5392_ = lean_usize_dec_eq(v___x_5390_, v___x_5391_);
if (v___x_5392_ == 0)
{
lean_object* v___x_5393_; 
lean_inc_ref(v_binderType_5367_);
lean_inc(v_binderName_5366_);
lean_dec_ref_known(v_e_5365_, 3);
v___x_5393_ = l_Lean_Expr_lam___override(v_binderName_5366_, v_binderType_5367_, v_b_x27_5370_, v_binderInfo_5369_);
return v___x_5393_;
}
else
{
size_t v___x_5394_; size_t v___x_5395_; uint8_t v___x_5396_; 
v___x_5394_ = lean_ptr_addr(v_body_5368_);
v___x_5395_ = lean_ptr_addr(v_b_x27_5370_);
v___x_5396_ = lean_usize_dec_eq(v___x_5394_, v___x_5395_);
if (v___x_5396_ == 0)
{
lean_object* v___x_5397_; 
lean_inc_ref(v_binderType_5367_);
lean_inc(v_binderName_5366_);
lean_dec_ref_known(v_e_5365_, 3);
v___x_5397_ = l_Lean_Expr_lam___override(v_binderName_5366_, v_binderType_5367_, v_b_x27_5370_, v_binderInfo_5369_);
return v___x_5397_;
}
else
{
uint8_t v___x_5398_; 
v___x_5398_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5369_, v_binderInfo_5369_);
if (v___x_5398_ == 0)
{
lean_object* v___x_5399_; 
lean_inc_ref(v_binderType_5367_);
lean_inc(v_binderName_5366_);
lean_dec_ref_known(v_e_5365_, 3);
v___x_5399_ = l_Lean_Expr_lam___override(v_binderName_5366_, v_binderType_5367_, v_b_x27_5370_, v_binderInfo_5369_);
return v___x_5399_;
}
else
{
lean_dec_ref_known(v_b_x27_5370_, 2);
return v_e_5365_;
}
}
}
}
}
}
else
{
goto v___jp_5371_;
}
}
else
{
goto v___jp_5371_;
}
v___jp_5371_:
{
size_t v___x_5372_; size_t v___x_5373_; uint8_t v___x_5374_; 
v___x_5372_ = lean_ptr_addr(v_binderType_5367_);
v___x_5373_ = lean_ptr_addr(v_binderType_5367_);
v___x_5374_ = lean_usize_dec_eq(v___x_5372_, v___x_5373_);
if (v___x_5374_ == 0)
{
lean_object* v___x_5375_; 
lean_inc_ref(v_binderType_5367_);
lean_inc(v_binderName_5366_);
lean_dec_ref_known(v_e_5365_, 3);
v___x_5375_ = l_Lean_Expr_lam___override(v_binderName_5366_, v_binderType_5367_, v_b_x27_5370_, v_binderInfo_5369_);
return v___x_5375_;
}
else
{
size_t v___x_5376_; size_t v___x_5377_; uint8_t v___x_5378_; 
v___x_5376_ = lean_ptr_addr(v_body_5368_);
v___x_5377_ = lean_ptr_addr(v_b_x27_5370_);
v___x_5378_ = lean_usize_dec_eq(v___x_5376_, v___x_5377_);
if (v___x_5378_ == 0)
{
lean_object* v___x_5379_; 
lean_inc_ref(v_binderType_5367_);
lean_inc(v_binderName_5366_);
lean_dec_ref_known(v_e_5365_, 3);
v___x_5379_ = l_Lean_Expr_lam___override(v_binderName_5366_, v_binderType_5367_, v_b_x27_5370_, v_binderInfo_5369_);
return v___x_5379_;
}
else
{
uint8_t v___x_5380_; 
v___x_5380_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5369_, v_binderInfo_5369_);
if (v___x_5380_ == 0)
{
lean_object* v___x_5381_; 
lean_inc_ref(v_binderType_5367_);
lean_inc(v_binderName_5366_);
lean_dec_ref_known(v_e_5365_, 3);
v___x_5381_ = l_Lean_Expr_lam___override(v_binderName_5366_, v_binderType_5367_, v_b_x27_5370_, v_binderInfo_5369_);
return v___x_5381_;
}
else
{
lean_dec_ref(v_b_x27_5370_);
return v_e_5365_;
}
}
}
}
}
else
{
return v_e_5365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5400_, lean_object* v_optionName_5401_, lean_object* v_inst_5402_, lean_object* v_val_5403_){
_start:
{
lean_object* v_toDataValue_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; 
v_toDataValue_5404_ = lean_ctor_get(v_inst_5402_, 0);
lean_inc_ref(v_toDataValue_5404_);
lean_dec_ref(v_inst_5402_);
v___x_5405_ = lean_box(0);
v___x_5406_ = lean_apply_1(v_toDataValue_5404_, v_val_5403_);
v___x_5407_ = l_Lean_KVMap_insert(v___x_5405_, v_optionName_5401_, v___x_5406_);
v___x_5408_ = l_Lean_Expr_mdata___override(v___x_5407_, v_e_5400_);
return v___x_5408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5409_, lean_object* v_e_5410_, lean_object* v_optionName_5411_, lean_object* v_inst_5412_, lean_object* v_val_5413_){
_start:
{
lean_object* v___x_5414_; 
v___x_5414_ = l_Lean_Expr_setOption___redArg(v_e_5410_, v_optionName_5411_, v_inst_5412_, v_val_5413_);
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5415_, lean_object* v_optionName_5416_, uint8_t v_val_5417_){
_start:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5418_ = lean_box(0);
v___x_5419_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5419_, 0, v_val_5417_);
v___x_5420_ = l_Lean_KVMap_insert(v___x_5418_, v_optionName_5416_, v___x_5419_);
v___x_5421_ = l_Lean_Expr_mdata___override(v___x_5420_, v_e_5415_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5422_, lean_object* v_optionName_5423_, lean_object* v_val_5424_){
_start:
{
uint8_t v_val_boxed_5425_; lean_object* v_res_5426_; 
v_val_boxed_5425_ = lean_unbox(v_val_5424_);
v_res_5426_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5422_, v_optionName_5423_, v_val_boxed_5425_);
return v_res_5426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5432_, uint8_t v_flag_5433_){
_start:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5434_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5435_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5432_, v___x_5434_, v_flag_5433_);
return v___x_5435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5436_, lean_object* v_flag_5437_){
_start:
{
uint8_t v_flag_boxed_5438_; lean_object* v_res_5439_; 
v_flag_boxed_5438_ = lean_unbox(v_flag_5437_);
v_res_5439_ = l_Lean_Expr_setPPExplicit(v_e_5436_, v_flag_boxed_5438_);
return v_res_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5444_, uint8_t v_flag_5445_){
_start:
{
lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___x_5446_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5447_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5444_, v___x_5446_, v_flag_5445_);
return v___x_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5448_, lean_object* v_flag_5449_){
_start:
{
uint8_t v_flag_boxed_5450_; lean_object* v_res_5451_; 
v_flag_boxed_5450_ = lean_unbox(v_flag_5449_);
v_res_5451_ = l_Lean_Expr_setPPUniverses(v_e_5448_, v_flag_boxed_5450_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5456_, uint8_t v_flag_5457_){
_start:
{
lean_object* v___x_5458_; lean_object* v___x_5459_; 
v___x_5458_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5459_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5456_, v___x_5458_, v_flag_5457_);
return v___x_5459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5460_, lean_object* v_flag_5461_){
_start:
{
uint8_t v_flag_boxed_5462_; lean_object* v_res_5463_; 
v_flag_boxed_5462_ = lean_unbox(v_flag_5461_);
v_res_5463_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5460_, v_flag_boxed_5462_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5468_, uint8_t v_flag_5469_){
_start:
{
lean_object* v___x_5470_; lean_object* v___x_5471_; 
v___x_5470_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5471_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5468_, v___x_5470_, v_flag_5469_);
return v___x_5471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5472_, lean_object* v_flag_5473_){
_start:
{
uint8_t v_flag_boxed_5474_; lean_object* v_res_5475_; 
v_flag_boxed_5474_ = lean_unbox(v_flag_5473_);
v_res_5475_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5472_, v_flag_boxed_5474_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5480_, uint8_t v_flag_5481_){
_start:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___x_5482_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5483_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5480_, v___x_5482_, v_flag_5481_);
return v___x_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5484_, lean_object* v_flag_5485_){
_start:
{
uint8_t v_flag_boxed_5486_; lean_object* v_res_5487_; 
v_flag_boxed_5486_ = lean_unbox(v_flag_5485_);
v_res_5487_ = l_Lean_Expr_setPPNumericTypes(v_e_5484_, v_flag_boxed_5486_);
return v_res_5487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5488_, size_t v_i_5489_, lean_object* v_bs_5490_){
_start:
{
uint8_t v___x_5491_; 
v___x_5491_ = lean_usize_dec_lt(v_i_5489_, v_sz_5488_);
if (v___x_5491_ == 0)
{
return v_bs_5490_;
}
else
{
uint8_t v___x_5492_; lean_object* v_v_5493_; lean_object* v___x_5494_; lean_object* v_bs_x27_5495_; lean_object* v___x_5496_; size_t v___x_5497_; size_t v___x_5498_; lean_object* v___x_5499_; 
v___x_5492_ = 0;
v_v_5493_ = lean_array_uget(v_bs_5490_, v_i_5489_);
v___x_5494_ = lean_unsigned_to_nat(0u);
v_bs_x27_5495_ = lean_array_uset(v_bs_5490_, v_i_5489_, v___x_5494_);
v___x_5496_ = l_Lean_Expr_setPPExplicit(v_v_5493_, v___x_5492_);
v___x_5497_ = ((size_t)1ULL);
v___x_5498_ = lean_usize_add(v_i_5489_, v___x_5497_);
v___x_5499_ = lean_array_uset(v_bs_x27_5495_, v_i_5489_, v___x_5496_);
v_i_5489_ = v___x_5498_;
v_bs_5490_ = v___x_5499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5501_, lean_object* v_i_5502_, lean_object* v_bs_5503_){
_start:
{
size_t v_sz_boxed_5504_; size_t v_i_boxed_5505_; lean_object* v_res_5506_; 
v_sz_boxed_5504_ = lean_unbox_usize(v_sz_5501_);
lean_dec(v_sz_5501_);
v_i_boxed_5505_ = lean_unbox_usize(v_i_5502_);
lean_dec(v_i_5502_);
v_res_5506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5504_, v_i_boxed_5505_, v_bs_5503_);
return v_res_5506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5507_){
_start:
{
if (lean_obj_tag(v_e_5507_) == 5)
{
lean_object* v___x_5508_; uint8_t v___x_5509_; lean_object* v_f_5510_; lean_object* v_dummy_5511_; lean_object* v_nargs_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; size_t v_sz_5517_; size_t v___x_5518_; lean_object* v_args_5519_; lean_object* v___x_5520_; uint8_t v___x_5521_; lean_object* v___x_5522_; 
v___x_5508_ = l_Lean_Expr_getAppFn(v_e_5507_);
v___x_5509_ = 0;
v_f_5510_ = l_Lean_Expr_setPPExplicit(v___x_5508_, v___x_5509_);
v_dummy_5511_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5512_ = l_Lean_Expr_getAppNumArgs(v_e_5507_);
lean_inc(v_nargs_5512_);
v___x_5513_ = lean_mk_array(v_nargs_5512_, v_dummy_5511_);
v___x_5514_ = lean_unsigned_to_nat(1u);
v___x_5515_ = lean_nat_sub(v_nargs_5512_, v___x_5514_);
lean_dec(v_nargs_5512_);
v___x_5516_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5507_, v___x_5513_, v___x_5515_);
v_sz_5517_ = lean_array_size(v___x_5516_);
v___x_5518_ = ((size_t)0ULL);
v_args_5519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5517_, v___x_5518_, v___x_5516_);
v___x_5520_ = l_Lean_mkAppN(v_f_5510_, v_args_5519_);
lean_dec_ref(v_args_5519_);
v___x_5521_ = 1;
v___x_5522_ = l_Lean_Expr_setPPExplicit(v___x_5520_, v___x_5521_);
return v___x_5522_;
}
else
{
return v_e_5507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5523_, size_t v_i_5524_, lean_object* v_bs_5525_){
_start:
{
uint8_t v___x_5526_; 
v___x_5526_ = lean_usize_dec_lt(v_i_5524_, v_sz_5523_);
if (v___x_5526_ == 0)
{
return v_bs_5525_;
}
else
{
lean_object* v_v_5527_; lean_object* v___x_5528_; lean_object* v_bs_x27_5529_; lean_object* v___y_5531_; uint8_t v___x_5536_; 
v_v_5527_ = lean_array_uget(v_bs_5525_, v_i_5524_);
v___x_5528_ = lean_unsigned_to_nat(0u);
v_bs_x27_5529_ = lean_array_uset(v_bs_5525_, v_i_5524_, v___x_5528_);
v___x_5536_ = l_Lean_Expr_hasMVar(v_v_5527_);
if (v___x_5536_ == 0)
{
lean_object* v___x_5537_; 
v___x_5537_ = l_Lean_Expr_setPPExplicit(v_v_5527_, v___x_5536_);
v___y_5531_ = v___x_5537_;
goto v___jp_5530_;
}
else
{
v___y_5531_ = v_v_5527_;
goto v___jp_5530_;
}
v___jp_5530_:
{
size_t v___x_5532_; size_t v___x_5533_; lean_object* v___x_5534_; 
v___x_5532_ = ((size_t)1ULL);
v___x_5533_ = lean_usize_add(v_i_5524_, v___x_5532_);
v___x_5534_ = lean_array_uset(v_bs_x27_5529_, v_i_5524_, v___y_5531_);
v_i_5524_ = v___x_5533_;
v_bs_5525_ = v___x_5534_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5538_, lean_object* v_i_5539_, lean_object* v_bs_5540_){
_start:
{
size_t v_sz_boxed_5541_; size_t v_i_boxed_5542_; lean_object* v_res_5543_; 
v_sz_boxed_5541_ = lean_unbox_usize(v_sz_5538_);
lean_dec(v_sz_5538_);
v_i_boxed_5542_ = lean_unbox_usize(v_i_5539_);
lean_dec(v_i_5539_);
v_res_5543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5541_, v_i_boxed_5542_, v_bs_5540_);
return v_res_5543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5544_){
_start:
{
if (lean_obj_tag(v_e_5544_) == 5)
{
lean_object* v___x_5545_; uint8_t v___x_5546_; lean_object* v_f_5547_; lean_object* v_dummy_5548_; lean_object* v_nargs_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; size_t v_sz_5554_; size_t v___x_5555_; lean_object* v_args_5556_; lean_object* v___x_5557_; uint8_t v___x_5558_; lean_object* v___x_5559_; 
v___x_5545_ = l_Lean_Expr_getAppFn(v_e_5544_);
v___x_5546_ = 0;
v_f_5547_ = l_Lean_Expr_setPPExplicit(v___x_5545_, v___x_5546_);
v_dummy_5548_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5549_ = l_Lean_Expr_getAppNumArgs(v_e_5544_);
lean_inc(v_nargs_5549_);
v___x_5550_ = lean_mk_array(v_nargs_5549_, v_dummy_5548_);
v___x_5551_ = lean_unsigned_to_nat(1u);
v___x_5552_ = lean_nat_sub(v_nargs_5549_, v___x_5551_);
lean_dec(v_nargs_5549_);
v___x_5553_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5544_, v___x_5550_, v___x_5552_);
v_sz_5554_ = lean_array_size(v___x_5553_);
v___x_5555_ = ((size_t)0ULL);
v_args_5556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5554_, v___x_5555_, v___x_5553_);
v___x_5557_ = l_Lean_mkAppN(v_f_5547_, v_args_5556_);
lean_dec_ref(v_args_5556_);
v___x_5558_ = 1;
v___x_5559_ = l_Lean_Expr_setPPExplicit(v___x_5557_, v___x_5558_);
return v___x_5559_;
}
else
{
return v_e_5544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5560_, lean_object* v_body_5561_, lean_object* v_x_5562_){
_start:
{
lean_object* v___x_5563_; 
v___x_5563_ = lean_apply_1(v_f_5560_, v_body_5561_);
return v___x_5563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5564_, lean_object* v_binderType_5565_, lean_object* v_x_5566_){
_start:
{
lean_object* v___x_5567_; 
v___x_5567_ = lean_apply_1(v_f_5564_, v_binderType_5565_);
return v___x_5567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5568_, lean_object* v_value_5569_, lean_object* v_x_5570_){
_start:
{
lean_object* v___x_5571_; 
v___x_5571_ = lean_apply_1(v_f_5568_, v_value_5569_);
return v___x_5571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5572_, lean_object* v_type_5573_, lean_object* v_x_5574_){
_start:
{
lean_object* v___x_5575_; 
v___x_5575_ = lean_apply_1(v_f_5572_, v_type_5573_);
return v___x_5575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5576_, lean_object* v_arg_5577_, lean_object* v_x_5578_){
_start:
{
lean_object* v___x_5579_; 
v___x_5579_ = lean_apply_1(v_f_5576_, v_arg_5577_);
return v___x_5579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5580_, lean_object* v_fn_5581_, lean_object* v_x_5582_){
_start:
{
lean_object* v___x_5583_; 
v___x_5583_ = lean_apply_1(v_f_5580_, v_fn_5581_);
return v___x_5583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5584_, lean_object* v_f_5585_, lean_object* v_x_5586_){
_start:
{
switch(lean_obj_tag(v_x_5586_))
{
case 7:
{
lean_object* v_toPure_5587_; lean_object* v_toSeq_5588_; lean_object* v_binderType_5589_; lean_object* v_body_5590_; lean_object* v___f_5591_; lean_object* v___f_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; 
v_toPure_5587_ = lean_ctor_get(v_inst_5584_, 1);
lean_inc(v_toPure_5587_);
v_toSeq_5588_ = lean_ctor_get(v_inst_5584_, 2);
lean_inc_n(v_toSeq_5588_, 2);
lean_dec_ref(v_inst_5584_);
v_binderType_5589_ = lean_ctor_get(v_x_5586_, 1);
v_body_5590_ = lean_ctor_get(v_x_5586_, 2);
lean_inc_ref(v_body_5590_);
lean_inc(v_f_5585_);
v___f_5591_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5591_, 0, v_f_5585_);
lean_closure_set(v___f_5591_, 1, v_body_5590_);
lean_inc_ref(v_binderType_5589_);
v___f_5592_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5592_, 0, v_f_5585_);
lean_closure_set(v___f_5592_, 1, v_binderType_5589_);
v___x_5593_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5593_, 0, v_x_5586_);
v___x_5594_ = lean_apply_2(v_toPure_5587_, lean_box(0), v___x_5593_);
v___x_5595_ = lean_apply_4(v_toSeq_5588_, lean_box(0), lean_box(0), v___x_5594_, v___f_5592_);
v___x_5596_ = lean_apply_4(v_toSeq_5588_, lean_box(0), lean_box(0), v___x_5595_, v___f_5591_);
return v___x_5596_;
}
case 6:
{
lean_object* v_toPure_5597_; lean_object* v_toSeq_5598_; lean_object* v_binderType_5599_; lean_object* v_body_5600_; lean_object* v___f_5601_; lean_object* v___f_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; 
v_toPure_5597_ = lean_ctor_get(v_inst_5584_, 1);
lean_inc(v_toPure_5597_);
v_toSeq_5598_ = lean_ctor_get(v_inst_5584_, 2);
lean_inc_n(v_toSeq_5598_, 2);
lean_dec_ref(v_inst_5584_);
v_binderType_5599_ = lean_ctor_get(v_x_5586_, 1);
v_body_5600_ = lean_ctor_get(v_x_5586_, 2);
lean_inc_ref(v_body_5600_);
lean_inc(v_f_5585_);
v___f_5601_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5601_, 0, v_f_5585_);
lean_closure_set(v___f_5601_, 1, v_body_5600_);
lean_inc_ref(v_binderType_5599_);
v___f_5602_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5602_, 0, v_f_5585_);
lean_closure_set(v___f_5602_, 1, v_binderType_5599_);
v___x_5603_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5603_, 0, v_x_5586_);
v___x_5604_ = lean_apply_2(v_toPure_5597_, lean_box(0), v___x_5603_);
v___x_5605_ = lean_apply_4(v_toSeq_5598_, lean_box(0), lean_box(0), v___x_5604_, v___f_5602_);
v___x_5606_ = lean_apply_4(v_toSeq_5598_, lean_box(0), lean_box(0), v___x_5605_, v___f_5601_);
return v___x_5606_;
}
case 10:
{
lean_object* v_toFunctor_5607_; lean_object* v_expr_5608_; lean_object* v_map_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; 
v_toFunctor_5607_ = lean_ctor_get(v_inst_5584_, 0);
lean_inc_ref(v_toFunctor_5607_);
lean_dec_ref(v_inst_5584_);
v_expr_5608_ = lean_ctor_get(v_x_5586_, 1);
lean_inc_ref(v_expr_5608_);
v_map_5609_ = lean_ctor_get(v_toFunctor_5607_, 0);
lean_inc(v_map_5609_);
lean_dec_ref(v_toFunctor_5607_);
v___x_5610_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5610_, 0, v_x_5586_);
v___x_5611_ = lean_apply_1(v_f_5585_, v_expr_5608_);
v___x_5612_ = lean_apply_4(v_map_5609_, lean_box(0), lean_box(0), v___x_5610_, v___x_5611_);
return v___x_5612_;
}
case 8:
{
lean_object* v_toPure_5613_; lean_object* v_toSeq_5614_; lean_object* v_type_5615_; lean_object* v_value_5616_; lean_object* v_body_5617_; lean_object* v___f_5618_; lean_object* v___f_5619_; lean_object* v___f_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; 
v_toPure_5613_ = lean_ctor_get(v_inst_5584_, 1);
lean_inc(v_toPure_5613_);
v_toSeq_5614_ = lean_ctor_get(v_inst_5584_, 2);
lean_inc_n(v_toSeq_5614_, 3);
lean_dec_ref(v_inst_5584_);
v_type_5615_ = lean_ctor_get(v_x_5586_, 1);
v_value_5616_ = lean_ctor_get(v_x_5586_, 2);
v_body_5617_ = lean_ctor_get(v_x_5586_, 3);
lean_inc_ref(v_body_5617_);
lean_inc_n(v_f_5585_, 2);
v___f_5618_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5618_, 0, v_f_5585_);
lean_closure_set(v___f_5618_, 1, v_body_5617_);
lean_inc_ref(v_value_5616_);
v___f_5619_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5619_, 0, v_f_5585_);
lean_closure_set(v___f_5619_, 1, v_value_5616_);
lean_inc_ref(v_type_5615_);
v___f_5620_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5620_, 0, v_f_5585_);
lean_closure_set(v___f_5620_, 1, v_type_5615_);
v___x_5621_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5621_, 0, v_x_5586_);
v___x_5622_ = lean_apply_2(v_toPure_5613_, lean_box(0), v___x_5621_);
v___x_5623_ = lean_apply_4(v_toSeq_5614_, lean_box(0), lean_box(0), v___x_5622_, v___f_5620_);
v___x_5624_ = lean_apply_4(v_toSeq_5614_, lean_box(0), lean_box(0), v___x_5623_, v___f_5619_);
v___x_5625_ = lean_apply_4(v_toSeq_5614_, lean_box(0), lean_box(0), v___x_5624_, v___f_5618_);
return v___x_5625_;
}
case 5:
{
lean_object* v_toPure_5626_; lean_object* v_toSeq_5627_; lean_object* v_fn_5628_; lean_object* v_arg_5629_; lean_object* v___f_5630_; lean_object* v___f_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; 
v_toPure_5626_ = lean_ctor_get(v_inst_5584_, 1);
lean_inc(v_toPure_5626_);
v_toSeq_5627_ = lean_ctor_get(v_inst_5584_, 2);
lean_inc_n(v_toSeq_5627_, 2);
lean_dec_ref(v_inst_5584_);
v_fn_5628_ = lean_ctor_get(v_x_5586_, 0);
v_arg_5629_ = lean_ctor_get(v_x_5586_, 1);
lean_inc_ref(v_arg_5629_);
lean_inc(v_f_5585_);
v___f_5630_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5630_, 0, v_f_5585_);
lean_closure_set(v___f_5630_, 1, v_arg_5629_);
lean_inc_ref(v_fn_5628_);
v___f_5631_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5631_, 0, v_f_5585_);
lean_closure_set(v___f_5631_, 1, v_fn_5628_);
v___x_5632_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5632_, 0, v_x_5586_);
v___x_5633_ = lean_apply_2(v_toPure_5626_, lean_box(0), v___x_5632_);
v___x_5634_ = lean_apply_4(v_toSeq_5627_, lean_box(0), lean_box(0), v___x_5633_, v___f_5631_);
v___x_5635_ = lean_apply_4(v_toSeq_5627_, lean_box(0), lean_box(0), v___x_5634_, v___f_5630_);
return v___x_5635_;
}
case 11:
{
lean_object* v_toFunctor_5636_; lean_object* v_struct_5637_; lean_object* v_map_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; 
v_toFunctor_5636_ = lean_ctor_get(v_inst_5584_, 0);
lean_inc_ref(v_toFunctor_5636_);
lean_dec_ref(v_inst_5584_);
v_struct_5637_ = lean_ctor_get(v_x_5586_, 2);
lean_inc_ref(v_struct_5637_);
v_map_5638_ = lean_ctor_get(v_toFunctor_5636_, 0);
lean_inc(v_map_5638_);
lean_dec_ref(v_toFunctor_5636_);
v___x_5639_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5639_, 0, v_x_5586_);
v___x_5640_ = lean_apply_1(v_f_5585_, v_struct_5637_);
v___x_5641_ = lean_apply_4(v_map_5638_, lean_box(0), lean_box(0), v___x_5639_, v___x_5640_);
return v___x_5641_;
}
default: 
{
lean_object* v_toPure_5642_; lean_object* v___x_5643_; 
lean_dec(v_f_5585_);
v_toPure_5642_ = lean_ctor_get(v_inst_5584_, 1);
lean_inc(v_toPure_5642_);
lean_dec_ref(v_inst_5584_);
v___x_5643_ = lean_apply_2(v_toPure_5642_, lean_box(0), v_x_5586_);
return v___x_5643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5644_, lean_object* v_inst_5645_, lean_object* v_f_5646_, lean_object* v_x_5647_){
_start:
{
lean_object* v___x_5648_; 
v___x_5648_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5645_, v_f_5646_, v_x_5647_);
return v___x_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5649_){
_start:
{
lean_object* v_snd_5650_; 
v_snd_5650_ = lean_ctor_get(v_self_5649_, 1);
lean_inc(v_snd_5650_);
return v_snd_5650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5651_){
_start:
{
lean_object* v_res_5652_; 
v_res_5652_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5651_);
lean_dec_ref(v_self_5651_);
return v_res_5652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5653_, lean_object* v_snd_5654_){
_start:
{
lean_object* v___x_5655_; 
v___x_5655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5655_, 0, v_e_x27_5653_);
lean_ctor_set(v___x_5655_, 1, v_snd_5654_);
return v___x_5655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5656_, lean_object* v_map_5657_, lean_object* v_e_x27_5658_, lean_object* v_a_5659_){
_start:
{
lean_object* v___f_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; 
lean_inc_ref(v_e_x27_5658_);
v___f_5660_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5660_, 0, v_e_x27_5658_);
v___x_5661_ = lean_apply_2(v_f_5656_, v_a_5659_, v_e_x27_5658_);
v___x_5662_ = lean_apply_4(v_map_5657_, lean_box(0), lean_box(0), v___f_5660_, v___x_5661_);
return v___x_5662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5664_, lean_object* v_f_5665_, lean_object* v_init_5666_, lean_object* v_e_5667_){
_start:
{
lean_object* v_toApplicative_5668_; lean_object* v_toFunctor_5669_; lean_object* v___x_5671_; uint8_t v_isShared_5672_; uint8_t v_isSharedCheck_5696_; 
v_toApplicative_5668_ = lean_ctor_get(v_inst_5664_, 0);
lean_inc_ref(v_toApplicative_5668_);
v_toFunctor_5669_ = lean_ctor_get(v_toApplicative_5668_, 0);
v_isSharedCheck_5696_ = !lean_is_exclusive(v_toApplicative_5668_);
if (v_isSharedCheck_5696_ == 0)
{
lean_object* v_unused_5697_; lean_object* v_unused_5698_; lean_object* v_unused_5699_; lean_object* v_unused_5700_; 
v_unused_5697_ = lean_ctor_get(v_toApplicative_5668_, 4);
lean_dec(v_unused_5697_);
v_unused_5698_ = lean_ctor_get(v_toApplicative_5668_, 3);
lean_dec(v_unused_5698_);
v_unused_5699_ = lean_ctor_get(v_toApplicative_5668_, 2);
lean_dec(v_unused_5699_);
v_unused_5700_ = lean_ctor_get(v_toApplicative_5668_, 1);
lean_dec(v_unused_5700_);
v___x_5671_ = v_toApplicative_5668_;
v_isShared_5672_ = v_isSharedCheck_5696_;
goto v_resetjp_5670_;
}
else
{
lean_inc(v_toFunctor_5669_);
lean_dec(v_toApplicative_5668_);
v___x_5671_ = lean_box(0);
v_isShared_5672_ = v_isSharedCheck_5696_;
goto v_resetjp_5670_;
}
v_resetjp_5670_:
{
lean_object* v_map_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5694_; 
v_map_5673_ = lean_ctor_get(v_toFunctor_5669_, 0);
v_isSharedCheck_5694_ = !lean_is_exclusive(v_toFunctor_5669_);
if (v_isSharedCheck_5694_ == 0)
{
lean_object* v_unused_5695_; 
v_unused_5695_ = lean_ctor_get(v_toFunctor_5669_, 1);
lean_dec(v_unused_5695_);
v___x_5675_ = v_toFunctor_5669_;
v_isShared_5676_ = v_isSharedCheck_5694_;
goto v_resetjp_5674_;
}
else
{
lean_inc(v_map_5673_);
lean_dec(v_toFunctor_5669_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5694_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
lean_object* v___f_5677_; lean_object* v___f_5678_; lean_object* v___f_5679_; lean_object* v___f_5680_; lean_object* v___f_5681_; lean_object* v___f_5682_; lean_object* v___x_5683_; lean_object* v___x_5685_; 
v___f_5677_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5673_);
v___f_5678_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5678_, 0, v_f_5665_);
lean_closure_set(v___f_5678_, 1, v_map_5673_);
lean_inc_ref_n(v_inst_5664_, 5);
v___f_5679_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5679_, 0, v_inst_5664_);
v___f_5680_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5680_, 0, v_inst_5664_);
v___f_5681_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5681_, 0, v_inst_5664_);
v___f_5682_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5682_, 0, v_inst_5664_);
v___x_5683_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5683_, 0, lean_box(0));
lean_closure_set(v___x_5683_, 1, lean_box(0));
lean_closure_set(v___x_5683_, 2, v_inst_5664_);
if (v_isShared_5676_ == 0)
{
lean_ctor_set(v___x_5675_, 1, v___f_5679_);
lean_ctor_set(v___x_5675_, 0, v___x_5683_);
v___x_5685_ = v___x_5675_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5693_; 
v_reuseFailAlloc_5693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5693_, 0, v___x_5683_);
lean_ctor_set(v_reuseFailAlloc_5693_, 1, v___f_5679_);
v___x_5685_ = v_reuseFailAlloc_5693_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
lean_object* v___x_5686_; lean_object* v___x_5688_; 
v___x_5686_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5686_, 0, lean_box(0));
lean_closure_set(v___x_5686_, 1, lean_box(0));
lean_closure_set(v___x_5686_, 2, v_inst_5664_);
if (v_isShared_5672_ == 0)
{
lean_ctor_set(v___x_5671_, 4, v___f_5682_);
lean_ctor_set(v___x_5671_, 3, v___f_5681_);
lean_ctor_set(v___x_5671_, 2, v___f_5680_);
lean_ctor_set(v___x_5671_, 1, v___x_5686_);
lean_ctor_set(v___x_5671_, 0, v___x_5685_);
v___x_5688_ = v___x_5671_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v___x_5685_);
lean_ctor_set(v_reuseFailAlloc_5692_, 1, v___x_5686_);
lean_ctor_set(v_reuseFailAlloc_5692_, 2, v___f_5680_);
lean_ctor_set(v_reuseFailAlloc_5692_, 3, v___f_5681_);
lean_ctor_set(v_reuseFailAlloc_5692_, 4, v___f_5682_);
v___x_5688_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
lean_object* v___x_30__overap_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; 
v___x_30__overap_5689_ = l_Lean_Expr_traverseChildren___redArg(v___x_5688_, v___f_5678_, v_e_5667_);
v___x_5690_ = lean_apply_1(v___x_30__overap_5689_, v_init_5666_);
v___x_5691_ = lean_apply_4(v_map_5673_, lean_box(0), lean_box(0), v___f_5677_, v___x_5690_);
return v___x_5691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5701_, lean_object* v_m_5702_, lean_object* v_inst_5703_, lean_object* v_f_5704_, lean_object* v_init_5705_, lean_object* v_e_5706_){
_start:
{
lean_object* v___x_5707_; 
v___x_5707_ = l_Lean_Expr_foldlM___redArg(v_inst_5703_, v_f_5704_, v_init_5705_, v_e_5706_);
return v___x_5707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5708_){
_start:
{
lean_object* v_d_5710_; lean_object* v_b_5711_; 
switch(lean_obj_tag(v_x_5708_))
{
case 5:
{
lean_object* v_fn_5717_; lean_object* v_arg_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; 
v_fn_5717_ = lean_ctor_get(v_x_5708_, 0);
v_arg_5718_ = lean_ctor_get(v_x_5708_, 1);
v___x_5719_ = lean_unsigned_to_nat(1u);
v___x_5720_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5717_);
v___x_5721_ = lean_nat_add(v___x_5719_, v___x_5720_);
lean_dec(v___x_5720_);
v___x_5722_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5718_);
v___x_5723_ = lean_nat_add(v___x_5721_, v___x_5722_);
lean_dec(v___x_5722_);
lean_dec(v___x_5721_);
return v___x_5723_;
}
case 6:
{
lean_object* v_binderType_5724_; lean_object* v_body_5725_; 
v_binderType_5724_ = lean_ctor_get(v_x_5708_, 1);
v_body_5725_ = lean_ctor_get(v_x_5708_, 2);
v_d_5710_ = v_binderType_5724_;
v_b_5711_ = v_body_5725_;
goto v___jp_5709_;
}
case 7:
{
lean_object* v_binderType_5726_; lean_object* v_body_5727_; 
v_binderType_5726_ = lean_ctor_get(v_x_5708_, 1);
v_body_5727_ = lean_ctor_get(v_x_5708_, 2);
v_d_5710_ = v_binderType_5726_;
v_b_5711_ = v_body_5727_;
goto v___jp_5709_;
}
case 8:
{
lean_object* v_type_5728_; lean_object* v_value_5729_; lean_object* v_body_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v_type_5728_ = lean_ctor_get(v_x_5708_, 1);
v_value_5729_ = lean_ctor_get(v_x_5708_, 2);
v_body_5730_ = lean_ctor_get(v_x_5708_, 3);
v___x_5731_ = lean_unsigned_to_nat(1u);
v___x_5732_ = l_Lean_Expr_sizeWithoutSharing(v_type_5728_);
v___x_5733_ = lean_nat_add(v___x_5731_, v___x_5732_);
lean_dec(v___x_5732_);
v___x_5734_ = l_Lean_Expr_sizeWithoutSharing(v_value_5729_);
v___x_5735_ = lean_nat_add(v___x_5733_, v___x_5734_);
lean_dec(v___x_5734_);
lean_dec(v___x_5733_);
v___x_5736_ = l_Lean_Expr_sizeWithoutSharing(v_body_5730_);
v___x_5737_ = lean_nat_add(v___x_5735_, v___x_5736_);
lean_dec(v___x_5736_);
lean_dec(v___x_5735_);
return v___x_5737_;
}
case 10:
{
lean_object* v_expr_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; 
v_expr_5738_ = lean_ctor_get(v_x_5708_, 1);
v___x_5739_ = lean_unsigned_to_nat(1u);
v___x_5740_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5738_);
v___x_5741_ = lean_nat_add(v___x_5739_, v___x_5740_);
lean_dec(v___x_5740_);
return v___x_5741_;
}
case 11:
{
lean_object* v_struct_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
v_struct_5742_ = lean_ctor_get(v_x_5708_, 2);
v___x_5743_ = lean_unsigned_to_nat(1u);
v___x_5744_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5742_);
v___x_5745_ = lean_nat_add(v___x_5743_, v___x_5744_);
lean_dec(v___x_5744_);
return v___x_5745_;
}
default: 
{
lean_object* v___x_5746_; 
v___x_5746_ = lean_unsigned_to_nat(1u);
return v___x_5746_;
}
}
v___jp_5709_:
{
lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; 
v___x_5712_ = lean_unsigned_to_nat(1u);
v___x_5713_ = l_Lean_Expr_sizeWithoutSharing(v_d_5710_);
v___x_5714_ = lean_nat_add(v___x_5712_, v___x_5713_);
lean_dec(v___x_5713_);
v___x_5715_ = l_Lean_Expr_sizeWithoutSharing(v_b_5711_);
v___x_5716_ = lean_nat_add(v___x_5714_, v___x_5715_);
lean_dec(v___x_5715_);
lean_dec(v___x_5714_);
return v___x_5716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5747_){
_start:
{
lean_object* v_res_5748_; 
v_res_5748_ = l_Lean_Expr_sizeWithoutSharing(v_x_5747_);
lean_dec_ref(v_x_5747_);
return v_res_5748_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5751_, lean_object* v_e_5752_){
_start:
{
lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___x_5753_ = l_Lean_KVMap_empty;
v___x_5754_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5755_ = l_Lean_KVMap_insert(v___x_5753_, v_kind_5751_, v___x_5754_);
v___x_5756_ = l_Lean_Expr_mdata___override(v___x_5755_, v_e_5752_);
return v___x_5756_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5757_, lean_object* v_e_5758_){
_start:
{
if (lean_obj_tag(v_e_5758_) == 10)
{
lean_object* v_data_5759_; lean_object* v_expr_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; uint8_t v___x_5763_; 
v_data_5759_ = lean_ctor_get(v_e_5758_, 0);
v_expr_5760_ = lean_ctor_get(v_e_5758_, 1);
v___x_5761_ = l_Lean_KVMap_size(v_data_5759_);
v___x_5762_ = lean_unsigned_to_nat(1u);
v___x_5763_ = lean_nat_dec_eq(v___x_5761_, v___x_5762_);
lean_dec(v___x_5761_);
if (v___x_5763_ == 0)
{
lean_object* v___x_5764_; 
v___x_5764_ = lean_box(0);
return v___x_5764_;
}
else
{
uint8_t v___x_5765_; uint8_t v___x_5766_; 
v___x_5765_ = 0;
v___x_5766_ = l_Lean_KVMap_getBool(v_data_5759_, v_kind_5757_, v___x_5765_);
if (v___x_5766_ == 0)
{
lean_object* v___x_5767_; 
v___x_5767_ = lean_box(0);
return v___x_5767_;
}
else
{
lean_object* v___x_5768_; 
lean_inc_ref(v_expr_5760_);
v___x_5768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5768_, 0, v_expr_5760_);
return v___x_5768_;
}
}
}
else
{
lean_object* v___x_5769_; 
v___x_5769_ = lean_box(0);
return v___x_5769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5770_, lean_object* v_e_5771_){
_start:
{
lean_object* v_res_5772_; 
v_res_5772_ = l_Lean_annotation_x3f(v_kind_5770_, v_e_5771_);
lean_dec_ref(v_e_5771_);
lean_dec(v_kind_5770_);
return v_res_5772_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5776_){
_start:
{
lean_object* v___x_5777_; lean_object* v___x_5778_; 
v___x_5777_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5778_ = l_Lean_mkAnnotation(v___x_5777_, v_e_5776_);
return v___x_5778_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5779_){
_start:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; 
v___x_5780_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5781_ = l_Lean_annotation_x3f(v___x_5780_, v_e_5779_);
return v___x_5781_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5782_){
_start:
{
lean_object* v_res_5783_; 
v_res_5783_ = l_Lean_inaccessible_x3f(v_e_5782_);
lean_dec_ref(v_e_5782_);
return v_res_5783_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5788_){
_start:
{
if (lean_obj_tag(v_p_5788_) == 10)
{
lean_object* v_data_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; 
v_data_5789_ = lean_ctor_get(v_p_5788_, 0);
v___x_5790_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5791_ = l_Lean_KVMap_find(v_data_5789_, v___x_5790_);
if (lean_obj_tag(v___x_5791_) == 1)
{
lean_object* v_val_5792_; lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5803_; 
v_val_5792_ = lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5803_ = !lean_is_exclusive(v___x_5791_);
if (v_isSharedCheck_5803_ == 0)
{
v___x_5794_ = v___x_5791_;
v_isShared_5795_ = v_isSharedCheck_5803_;
goto v_resetjp_5793_;
}
else
{
lean_inc(v_val_5792_);
lean_dec(v___x_5791_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5803_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
if (lean_obj_tag(v_val_5792_) == 5)
{
lean_object* v_v_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5800_; 
v_v_5796_ = lean_ctor_get(v_val_5792_, 0);
lean_inc(v_v_5796_);
lean_dec_ref_known(v_val_5792_, 1);
v___x_5797_ = l_Lean_Expr_mdataExpr_x21(v_p_5788_);
v___x_5798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5798_, 0, v_v_5796_);
lean_ctor_set(v___x_5798_, 1, v___x_5797_);
if (v_isShared_5795_ == 0)
{
lean_ctor_set(v___x_5794_, 0, v___x_5798_);
v___x_5800_ = v___x_5794_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v___x_5798_);
v___x_5800_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
return v___x_5800_;
}
}
else
{
lean_object* v___x_5802_; 
lean_del_object(v___x_5794_);
lean_dec(v_val_5792_);
v___x_5802_ = lean_box(0);
return v___x_5802_;
}
}
}
else
{
lean_object* v___x_5804_; 
lean_dec(v___x_5791_);
v___x_5804_ = lean_box(0);
return v___x_5804_;
}
}
else
{
lean_object* v___x_5805_; 
v___x_5805_ = lean_box(0);
return v___x_5805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5806_){
_start:
{
lean_object* v_res_5807_; 
v_res_5807_ = l_Lean_patternWithRef_x3f(v_p_5806_);
lean_dec_ref(v_p_5806_);
return v_res_5807_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5808_){
_start:
{
lean_object* v___x_5809_; 
v___x_5809_ = l_Lean_patternWithRef_x3f(v_p_5808_);
if (lean_obj_tag(v___x_5809_) == 0)
{
uint8_t v___x_5810_; 
v___x_5810_ = 0;
return v___x_5810_;
}
else
{
uint8_t v___x_5811_; 
lean_dec_ref_known(v___x_5809_, 1);
v___x_5811_ = 1;
return v___x_5811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5812_){
_start:
{
uint8_t v_res_5813_; lean_object* v_r_5814_; 
v_res_5813_ = l_Lean_isPatternWithRef(v_p_5812_);
lean_dec_ref(v_p_5812_);
v_r_5814_ = lean_box(v_res_5813_);
return v_r_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5815_, lean_object* v_stx_5816_){
_start:
{
lean_object* v___x_5817_; 
v___x_5817_ = l_Lean_patternWithRef_x3f(v_p_5815_);
if (lean_obj_tag(v___x_5817_) == 0)
{
lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5818_ = l_Lean_KVMap_empty;
v___x_5819_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5820_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5820_, 0, v_stx_5816_);
v___x_5821_ = l_Lean_KVMap_insert(v___x_5818_, v___x_5819_, v___x_5820_);
v___x_5822_ = l_Lean_Expr_mdata___override(v___x_5821_, v_p_5815_);
return v___x_5822_;
}
else
{
lean_dec_ref_known(v___x_5817_, 1);
lean_dec(v_stx_5816_);
return v_p_5815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5823_){
_start:
{
lean_object* v___x_5824_; 
v___x_5824_ = l_Lean_inaccessible_x3f(v_e_5823_);
if (lean_obj_tag(v___x_5824_) == 1)
{
return v___x_5824_;
}
else
{
lean_object* v___x_5825_; 
lean_dec(v___x_5824_);
v___x_5825_ = l_Lean_patternWithRef_x3f(v_e_5823_);
if (lean_obj_tag(v___x_5825_) == 1)
{
lean_object* v_val_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5834_; 
v_val_5826_ = lean_ctor_get(v___x_5825_, 0);
v_isSharedCheck_5834_ = !lean_is_exclusive(v___x_5825_);
if (v_isSharedCheck_5834_ == 0)
{
v___x_5828_ = v___x_5825_;
v_isShared_5829_ = v_isSharedCheck_5834_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_val_5826_);
lean_dec(v___x_5825_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5834_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
lean_object* v_snd_5830_; lean_object* v___x_5832_; 
v_snd_5830_ = lean_ctor_get(v_val_5826_, 1);
lean_inc(v_snd_5830_);
lean_dec(v_val_5826_);
if (v_isShared_5829_ == 0)
{
lean_ctor_set(v___x_5828_, 0, v_snd_5830_);
v___x_5832_ = v___x_5828_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5833_; 
v_reuseFailAlloc_5833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5833_, 0, v_snd_5830_);
v___x_5832_ = v_reuseFailAlloc_5833_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
return v___x_5832_;
}
}
}
else
{
lean_object* v___x_5835_; 
lean_dec(v___x_5825_);
v___x_5835_ = lean_box(0);
return v___x_5835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5836_){
_start:
{
lean_object* v_res_5837_; 
v_res_5837_ = l_Lean_patternAnnotation_x3f(v_e_5836_);
lean_dec_ref(v_e_5836_);
return v_res_5837_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5841_){
_start:
{
lean_object* v___x_5842_; lean_object* v___x_5843_; 
v___x_5842_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5843_ = l_Lean_mkAnnotation(v___x_5842_, v_e_5841_);
return v___x_5843_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5847_){
_start:
{
lean_object* v___x_5848_; lean_object* v___x_5849_; 
v___x_5848_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5849_ = l_Lean_annotation_x3f(v___x_5848_, v_e_5847_);
if (lean_obj_tag(v___x_5849_) == 0)
{
return v___x_5849_;
}
else
{
lean_object* v_val_5850_; lean_object* v___x_5852_; uint8_t v_isShared_5853_; uint8_t v_isSharedCheck_5863_; 
v_val_5850_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5863_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5863_ == 0)
{
v___x_5852_ = v___x_5849_;
v_isShared_5853_ = v_isSharedCheck_5863_;
goto v_resetjp_5851_;
}
else
{
lean_inc(v_val_5850_);
lean_dec(v___x_5849_);
v___x_5852_ = lean_box(0);
v_isShared_5853_ = v_isSharedCheck_5863_;
goto v_resetjp_5851_;
}
v_resetjp_5851_:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; uint8_t v___x_5856_; 
v___x_5854_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5855_ = lean_unsigned_to_nat(3u);
v___x_5856_ = l_Lean_Expr_isAppOfArity(v_val_5850_, v___x_5854_, v___x_5855_);
if (v___x_5856_ == 0)
{
lean_object* v___x_5857_; 
lean_del_object(v___x_5852_);
lean_dec(v_val_5850_);
v___x_5857_ = lean_box(0);
return v___x_5857_;
}
else
{
lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5861_; 
v___x_5858_ = l_Lean_Expr_appFn_x21(v_val_5850_);
lean_dec(v_val_5850_);
v___x_5859_ = l_Lean_Expr_appArg_x21(v___x_5858_);
lean_dec_ref(v___x_5858_);
if (v_isShared_5853_ == 0)
{
lean_ctor_set(v___x_5852_, 0, v___x_5859_);
v___x_5861_ = v___x_5852_;
goto v_reusejp_5860_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v___x_5859_);
v___x_5861_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5860_;
}
v_reusejp_5860_:
{
return v___x_5861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5864_){
_start:
{
lean_object* v_res_5865_; 
v_res_5865_ = l_Lean_isLHSGoal_x3f(v_e_5864_);
lean_dec_ref(v_e_5864_);
return v_res_5865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5866_, lean_object* v_____do__lift_5867_){
_start:
{
lean_object* v___x_5868_; 
v___x_5868_ = lean_apply_2(v_toPure_5866_, lean_box(0), v_____do__lift_5867_);
return v___x_5868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5869_, lean_object* v_inst_5870_){
_start:
{
lean_object* v_toApplicative_5871_; lean_object* v_toBind_5872_; lean_object* v_toPure_5873_; lean_object* v___x_5874_; lean_object* v___f_5875_; lean_object* v___x_5876_; 
v_toApplicative_5871_ = lean_ctor_get(v_inst_5869_, 0);
v_toBind_5872_ = lean_ctor_get(v_inst_5869_, 1);
lean_inc(v_toBind_5872_);
v_toPure_5873_ = lean_ctor_get(v_toApplicative_5871_, 1);
lean_inc(v_toPure_5873_);
v___x_5874_ = l_Lean_mkFreshId___redArg(v_inst_5869_, v_inst_5870_);
v___f_5875_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5875_, 0, v_toPure_5873_);
v___x_5876_ = lean_apply_4(v_toBind_5872_, lean_box(0), lean_box(0), v___x_5874_, v___f_5875_);
return v___x_5876_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5877_, lean_object* v_inst_5878_, lean_object* v_inst_5879_){
_start:
{
lean_object* v___x_5880_; 
v___x_5880_ = l_Lean_mkFreshFVarId___redArg(v_inst_5878_, v_inst_5879_);
return v___x_5880_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5881_, lean_object* v_inst_5882_){
_start:
{
lean_object* v_toApplicative_5883_; lean_object* v_toBind_5884_; lean_object* v_toPure_5885_; lean_object* v___x_5886_; lean_object* v___f_5887_; lean_object* v___x_5888_; 
v_toApplicative_5883_ = lean_ctor_get(v_inst_5881_, 0);
v_toBind_5884_ = lean_ctor_get(v_inst_5881_, 1);
lean_inc(v_toBind_5884_);
v_toPure_5885_ = lean_ctor_get(v_toApplicative_5883_, 1);
lean_inc(v_toPure_5885_);
v___x_5886_ = l_Lean_mkFreshId___redArg(v_inst_5881_, v_inst_5882_);
v___f_5887_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5887_, 0, v_toPure_5885_);
v___x_5888_ = lean_apply_4(v_toBind_5884_, lean_box(0), lean_box(0), v___x_5886_, v___f_5887_);
return v___x_5888_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5889_, lean_object* v_inst_5890_, lean_object* v_inst_5891_){
_start:
{
lean_object* v___x_5892_; 
v___x_5892_ = l_Lean_mkFreshMVarId___redArg(v_inst_5890_, v_inst_5891_);
return v___x_5892_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5893_, lean_object* v_inst_5894_){
_start:
{
lean_object* v_toApplicative_5895_; lean_object* v_toBind_5896_; lean_object* v_toPure_5897_; lean_object* v___x_5898_; lean_object* v___f_5899_; lean_object* v___x_5900_; 
v_toApplicative_5895_ = lean_ctor_get(v_inst_5893_, 0);
v_toBind_5896_ = lean_ctor_get(v_inst_5893_, 1);
lean_inc(v_toBind_5896_);
v_toPure_5897_ = lean_ctor_get(v_toApplicative_5895_, 1);
lean_inc(v_toPure_5897_);
v___x_5898_ = l_Lean_mkFreshId___redArg(v_inst_5893_, v_inst_5894_);
v___f_5899_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5899_, 0, v_toPure_5897_);
v___x_5900_ = lean_apply_4(v_toBind_5896_, lean_box(0), lean_box(0), v___x_5898_, v___f_5899_);
return v___x_5900_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5901_, lean_object* v_inst_5902_, lean_object* v_inst_5903_){
_start:
{
lean_object* v___x_5904_; 
v___x_5904_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5902_, v_inst_5903_);
return v___x_5904_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; 
v___x_5908_ = lean_box(0);
v___x_5909_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5910_ = l_Lean_Expr_const___override(v___x_5909_, v___x_5908_);
return v___x_5910_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5911_){
_start:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5912_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5913_ = l_Lean_Expr_app___override(v___x_5912_, v_p_5911_);
return v___x_5913_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; 
v___x_5917_ = lean_box(0);
v___x_5918_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5919_ = l_Lean_Expr_const___override(v___x_5918_, v___x_5917_);
return v___x_5919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5920_, lean_object* v_q_5921_){
_start:
{
lean_object* v___x_5922_; lean_object* v___x_5923_; 
v___x_5922_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5923_ = l_Lean_mkAppB(v___x_5922_, v_p_5920_, v_q_5921_);
return v___x_5923_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5927_ = lean_box(0);
v___x_5928_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5929_ = l_Lean_Expr_const___override(v___x_5928_, v___x_5927_);
return v___x_5929_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5930_, lean_object* v_q_5931_){
_start:
{
lean_object* v___x_5932_; lean_object* v___x_5933_; 
v___x_5932_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5933_ = l_Lean_mkAppB(v___x_5932_, v_p_5930_, v_q_5931_);
return v___x_5933_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___x_5934_ = lean_box(0);
v___x_5935_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5936_ = l_Lean_Expr_const___override(v___x_5935_, v___x_5934_);
return v___x_5936_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5937_){
_start:
{
if (lean_obj_tag(v_x_5937_) == 0)
{
lean_object* v___x_5938_; 
v___x_5938_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5938_;
}
else
{
lean_object* v_tail_5939_; 
v_tail_5939_ = lean_ctor_get(v_x_5937_, 1);
if (lean_obj_tag(v_tail_5939_) == 0)
{
lean_object* v_head_5940_; 
v_head_5940_ = lean_ctor_get(v_x_5937_, 0);
lean_inc(v_head_5940_);
lean_dec_ref_known(v_x_5937_, 2);
return v_head_5940_;
}
else
{
lean_object* v_head_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; 
lean_inc(v_tail_5939_);
v_head_5941_ = lean_ctor_get(v_x_5937_, 0);
lean_inc(v_head_5941_);
lean_dec_ref_known(v_x_5937_, 2);
v___x_5942_ = l_Lean_mkAndN(v_tail_5939_);
v___x_5943_ = l_Lean_mkAnd(v_head_5941_, v___x_5942_);
return v___x_5943_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; 
v___x_5949_ = lean_box(0);
v___x_5950_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5951_ = l_Lean_Expr_const___override(v___x_5950_, v___x_5949_);
return v___x_5951_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5952_){
_start:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; 
v___x_5953_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5954_ = l_Lean_Expr_app___override(v___x_5953_, v_p_5952_);
return v___x_5954_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; 
v___x_5958_ = lean_box(0);
v___x_5959_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5960_ = l_Lean_Expr_const___override(v___x_5959_, v___x_5958_);
return v___x_5960_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5961_, lean_object* v_q_5962_){
_start:
{
lean_object* v___x_5963_; lean_object* v___x_5964_; 
v___x_5963_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5964_ = l_Lean_mkAppB(v___x_5963_, v_p_5961_, v_q_5962_);
return v___x_5964_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5965_; 
v___x_5965_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5965_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; 
v___x_5969_ = lean_box(0);
v___x_5970_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5971_ = l_Lean_Expr_const___override(v___x_5970_, v___x_5969_);
return v___x_5971_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5972_; 
v___x_5972_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5972_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
v___x_5976_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5977_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5978_ = l_Lean_Expr_const___override(v___x_5977_, v___x_5976_);
return v___x_5978_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; 
v___x_5979_ = l_Lean_Nat_mkInstAdd;
v___x_5980_ = l_Lean_Nat_mkType;
v___x_5981_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5982_ = l_Lean_mkAppB(v___x_5981_, v___x_5980_, v___x_5979_);
return v___x_5982_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5983_; 
v___x_5983_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5983_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; 
v___x_5987_ = lean_box(0);
v___x_5988_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5989_ = l_Lean_Expr_const___override(v___x_5988_, v___x_5987_);
return v___x_5989_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5990_; 
v___x_5990_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5990_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; 
v___x_5994_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5995_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5996_ = l_Lean_Expr_const___override(v___x_5995_, v___x_5994_);
return v___x_5996_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; 
v___x_5997_ = l_Lean_Nat_mkInstSub;
v___x_5998_ = l_Lean_Nat_mkType;
v___x_5999_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6000_ = l_Lean_mkAppB(v___x_5999_, v___x_5998_, v___x_5997_);
return v___x_6000_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_6001_; 
v___x_6001_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_6001_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6005_ = lean_box(0);
v___x_6006_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_6007_ = l_Lean_Expr_const___override(v___x_6006_, v___x_6005_);
return v___x_6007_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_6008_; 
v___x_6008_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_6008_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; 
v___x_6012_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6013_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_6014_ = l_Lean_Expr_const___override(v___x_6013_, v___x_6012_);
return v___x_6014_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; 
v___x_6015_ = l_Lean_Nat_mkInstMul;
v___x_6016_ = l_Lean_Nat_mkType;
v___x_6017_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6018_ = l_Lean_mkAppB(v___x_6017_, v___x_6016_, v___x_6015_);
return v___x_6018_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_6019_; 
v___x_6019_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_6019_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; 
v___x_6024_ = lean_box(0);
v___x_6025_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_6026_ = l_Lean_Expr_const___override(v___x_6025_, v___x_6024_);
return v___x_6026_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_6027_; 
v___x_6027_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_6027_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; 
v___x_6031_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6032_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_6033_ = l_Lean_Expr_const___override(v___x_6032_, v___x_6031_);
return v___x_6033_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; 
v___x_6034_ = l_Lean_Nat_mkInstDiv;
v___x_6035_ = l_Lean_Nat_mkType;
v___x_6036_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6037_ = l_Lean_mkAppB(v___x_6036_, v___x_6035_, v___x_6034_);
return v___x_6037_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_6038_; 
v___x_6038_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_6038_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; 
v___x_6043_ = lean_box(0);
v___x_6044_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_6045_ = l_Lean_Expr_const___override(v___x_6044_, v___x_6043_);
return v___x_6045_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_6046_; 
v___x_6046_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_6046_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; 
v___x_6050_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6051_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_6052_ = l_Lean_Expr_const___override(v___x_6051_, v___x_6050_);
return v___x_6052_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; 
v___x_6053_ = l_Lean_Nat_mkInstMod;
v___x_6054_ = l_Lean_Nat_mkType;
v___x_6055_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6056_ = l_Lean_mkAppB(v___x_6055_, v___x_6054_, v___x_6053_);
return v___x_6056_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_6057_; 
v___x_6057_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_6057_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; 
v___x_6061_ = lean_box(0);
v___x_6062_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_6063_ = l_Lean_Expr_const___override(v___x_6062_, v___x_6061_);
return v___x_6063_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_6064_; 
v___x_6064_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_6064_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; 
v___x_6068_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6069_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_6070_ = l_Lean_Expr_const___override(v___x_6069_, v___x_6068_);
return v___x_6070_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6071_ = l_Lean_Nat_mkInstNatPow;
v___x_6072_ = l_Lean_Nat_mkType;
v___x_6073_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6074_ = l_Lean_mkAppB(v___x_6073_, v___x_6072_, v___x_6071_);
return v___x_6074_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_6075_; 
v___x_6075_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_6075_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; 
v___x_6082_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_6083_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_6084_ = l_Lean_Expr_const___override(v___x_6083_, v___x_6082_);
return v___x_6084_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; 
v___x_6085_ = l_Lean_Nat_mkInstPow;
v___x_6086_ = l_Lean_Nat_mkType;
v___x_6087_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6088_ = l_Lean_mkApp3(v___x_6087_, v___x_6086_, v___x_6086_, v___x_6085_);
return v___x_6088_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_6089_; 
v___x_6089_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_6089_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; 
v___x_6093_ = lean_box(0);
v___x_6094_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_6095_ = l_Lean_Expr_const___override(v___x_6094_, v___x_6093_);
return v___x_6095_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_6096_; 
v___x_6096_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_6096_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6100_ = lean_box(0);
v___x_6101_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6102_ = l_Lean_Expr_const___override(v___x_6101_, v___x_6100_);
return v___x_6102_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6103_; 
v___x_6103_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6103_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6109_; lean_object* v___x_6110_; 
v___x_6109_ = lean_unsigned_to_nat(0u);
v___x_6110_ = l_Lean_Level_ofNat(v___x_6109_);
return v___x_6110_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; 
v___x_6111_ = lean_box(0);
v___x_6112_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
lean_ctor_set(v___x_6113_, 1, v___x_6111_);
return v___x_6113_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; 
v___x_6114_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6115_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6115_);
lean_ctor_set(v___x_6116_, 1, v___x_6114_);
return v___x_6116_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; 
v___x_6117_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6118_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6118_);
lean_ctor_set(v___x_6119_, 1, v___x_6117_);
return v___x_6119_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; 
v___x_6120_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6121_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6122_ = l_Lean_Expr_const___override(v___x_6121_, v___x_6120_);
return v___x_6122_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; 
v___x_6123_ = l_Lean_Nat_mkInstHAdd;
v___x_6124_ = l_Lean_Nat_mkType;
v___x_6125_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6126_ = l_Lean_mkApp4(v___x_6125_, v___x_6124_, v___x_6124_, v___x_6124_, v___x_6123_);
return v___x_6126_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6127_; 
v___x_6127_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6127_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6133_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6134_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6135_ = l_Lean_Expr_const___override(v___x_6134_, v___x_6133_);
return v___x_6135_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; 
v___x_6136_ = l_Lean_Nat_mkInstHSub;
v___x_6137_ = l_Lean_Nat_mkType;
v___x_6138_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6139_ = l_Lean_mkApp4(v___x_6138_, v___x_6137_, v___x_6137_, v___x_6137_, v___x_6136_);
return v___x_6139_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6140_; 
v___x_6140_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6140_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6146_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6147_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6148_ = l_Lean_Expr_const___override(v___x_6147_, v___x_6146_);
return v___x_6148_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; 
v___x_6149_ = l_Lean_Nat_mkInstHMul;
v___x_6150_ = l_Lean_Nat_mkType;
v___x_6151_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6152_ = l_Lean_mkApp4(v___x_6151_, v___x_6150_, v___x_6150_, v___x_6150_, v___x_6149_);
return v___x_6152_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6153_; 
v___x_6153_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6153_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; 
v___x_6159_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6160_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6161_ = l_Lean_Expr_const___override(v___x_6160_, v___x_6159_);
return v___x_6161_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; 
v___x_6162_ = l_Lean_Nat_mkInstHPow;
v___x_6163_ = l_Lean_Nat_mkType;
v___x_6164_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6165_ = l_Lean_mkApp4(v___x_6164_, v___x_6163_, v___x_6163_, v___x_6163_, v___x_6162_);
return v___x_6165_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6166_; 
v___x_6166_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6166_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6171_ = lean_box(0);
v___x_6172_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6173_ = l_Lean_Expr_const___override(v___x_6172_, v___x_6171_);
return v___x_6173_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6174_){
_start:
{
lean_object* v___x_6175_; lean_object* v___x_6176_; 
v___x_6175_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6176_ = l_Lean_Expr_app___override(v___x_6175_, v_a_6174_);
return v___x_6176_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6177_, lean_object* v_b_6178_){
_start:
{
lean_object* v___x_6179_; lean_object* v___x_6180_; 
v___x_6179_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6180_ = l_Lean_mkAppB(v___x_6179_, v_a_6177_, v_b_6178_);
return v___x_6180_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6181_, lean_object* v_b_6182_){
_start:
{
lean_object* v___x_6183_; lean_object* v___x_6184_; 
v___x_6183_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6184_ = l_Lean_mkAppB(v___x_6183_, v_a_6181_, v_b_6182_);
return v___x_6184_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6185_, lean_object* v_b_6186_){
_start:
{
lean_object* v___x_6187_; lean_object* v___x_6188_; 
v___x_6187_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6188_ = l_Lean_mkAppB(v___x_6187_, v_a_6185_, v_b_6186_);
return v___x_6188_;
}
}
static lean_object* _init_l_Lean_mkNatDiv___closed__3(void){
_start:
{
lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6194_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6195_ = ((lean_object*)(l_Lean_mkNatDiv___closed__2));
v___x_6196_ = l_Lean_Expr_const___override(v___x_6195_, v___x_6194_);
return v___x_6196_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatDiv(lean_object* v_a_6197_, lean_object* v_b_6198_){
_start:
{
lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6199_ = lean_obj_once(&l_Lean_mkNatDiv___closed__3, &l_Lean_mkNatDiv___closed__3_once, _init_l_Lean_mkNatDiv___closed__3);
v___x_6200_ = l_Lean_Nat_mkType;
v___x_6201_ = l_Lean_Nat_mkInstHDiv;
v___x_6202_ = l_Lean_mkApp6(v___x_6199_, v___x_6200_, v___x_6200_, v___x_6200_, v___x_6201_, v_a_6197_, v_b_6198_);
return v___x_6202_;
}
}
static lean_object* _init_l_Lean_mkNatMod___closed__3(void){
_start:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; 
v___x_6208_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6209_ = ((lean_object*)(l_Lean_mkNatMod___closed__2));
v___x_6210_ = l_Lean_Expr_const___override(v___x_6209_, v___x_6208_);
return v___x_6210_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMod(lean_object* v_a_6211_, lean_object* v_b_6212_){
_start:
{
lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; 
v___x_6213_ = lean_obj_once(&l_Lean_mkNatMod___closed__3, &l_Lean_mkNatMod___closed__3_once, _init_l_Lean_mkNatMod___closed__3);
v___x_6214_ = l_Lean_Nat_mkType;
v___x_6215_ = l_Lean_Nat_mkInstHMod;
v___x_6216_ = l_Lean_mkApp6(v___x_6213_, v___x_6214_, v___x_6214_, v___x_6214_, v___x_6215_, v_a_6211_, v_b_6212_);
return v___x_6216_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6217_, lean_object* v_b_6218_){
_start:
{
lean_object* v___x_6219_; lean_object* v___x_6220_; 
v___x_6219_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6220_ = l_Lean_mkAppB(v___x_6219_, v_a_6217_, v_b_6218_);
return v___x_6220_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; 
v___x_6226_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6227_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6228_ = l_Lean_Expr_const___override(v___x_6227_, v___x_6226_);
return v___x_6228_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; 
v___x_6229_ = l_Lean_Nat_mkInstLE;
v___x_6230_ = l_Lean_Nat_mkType;
v___x_6231_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6232_ = l_Lean_mkAppB(v___x_6231_, v___x_6230_, v___x_6229_);
return v___x_6232_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6233_; 
v___x_6233_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6233_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6234_, lean_object* v_b_6235_){
_start:
{
lean_object* v___x_6236_; lean_object* v___x_6237_; 
v___x_6236_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6237_ = l_Lean_mkAppB(v___x_6236_, v_a_6234_, v_b_6235_);
return v___x_6237_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6238_; lean_object* v___x_6239_; 
v___x_6238_ = lean_unsigned_to_nat(1u);
v___x_6239_ = l_Lean_Level_ofNat(v___x_6238_);
return v___x_6239_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; 
v___x_6240_ = lean_box(0);
v___x_6241_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6242_, 0, v___x_6241_);
lean_ctor_set(v___x_6242_, 1, v___x_6240_);
return v___x_6242_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; 
v___x_6243_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6244_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6245_ = l_Lean_Expr_const___override(v___x_6244_, v___x_6243_);
return v___x_6245_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6246_; lean_object* v___x_6247_; lean_object* v___x_6248_; 
v___x_6246_ = l_Lean_Nat_mkType;
v___x_6247_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6248_ = l_Lean_Expr_app___override(v___x_6247_, v___x_6246_);
return v___x_6248_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6249_; 
v___x_6249_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6249_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6250_, lean_object* v_b_6251_){
_start:
{
lean_object* v___x_6252_; lean_object* v___x_6253_; 
v___x_6252_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6253_ = l_Lean_mkAppB(v___x_6252_, v_a_6250_, v_b_6251_);
return v___x_6253_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6254_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6255_ = l_Lean_Expr_sort___override(v___x_6254_);
return v___x_6255_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; 
v___x_6256_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6257_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6258_ = l_Lean_Expr_app___override(v___x_6257_, v___x_6256_);
return v___x_6258_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6259_; 
v___x_6259_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6259_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6260_, lean_object* v_b_6261_){
_start:
{
lean_object* v___x_6262_; lean_object* v___x_6263_; 
v___x_6262_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6263_ = l_Lean_mkAppB(v___x_6262_, v_a_6260_, v_b_6261_);
return v___x_6263_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; 
v___x_6267_ = lean_box(0);
v___x_6268_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6269_ = l_Lean_Expr_const___override(v___x_6268_, v___x_6267_);
return v___x_6269_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6270_; 
v___x_6270_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6270_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; 
v___x_6275_ = lean_box(0);
v___x_6276_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6277_ = l_Lean_Expr_const___override(v___x_6276_, v___x_6275_);
return v___x_6277_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6278_; 
v___x_6278_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6278_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; 
v___x_6283_ = lean_box(0);
v___x_6284_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6285_ = l_Lean_Expr_const___override(v___x_6284_, v___x_6283_);
return v___x_6285_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6286_; 
v___x_6286_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6286_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; 
v___x_6287_ = l_Lean_Int_mkInstAdd;
v___x_6288_ = l_Lean_Int_mkType;
v___x_6289_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6290_ = l_Lean_mkAppB(v___x_6289_, v___x_6288_, v___x_6287_);
return v___x_6290_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6291_; 
v___x_6291_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6291_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; 
v___x_6296_ = lean_box(0);
v___x_6297_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6298_ = l_Lean_Expr_const___override(v___x_6297_, v___x_6296_);
return v___x_6298_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6299_; 
v___x_6299_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6299_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; 
v___x_6300_ = l_Lean_Int_mkInstSub;
v___x_6301_ = l_Lean_Int_mkType;
v___x_6302_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6303_ = l_Lean_mkAppB(v___x_6302_, v___x_6301_, v___x_6300_);
return v___x_6303_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6304_; 
v___x_6304_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6304_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6311_; 
v___x_6309_ = lean_box(0);
v___x_6310_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6311_ = l_Lean_Expr_const___override(v___x_6310_, v___x_6309_);
return v___x_6311_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6312_; 
v___x_6312_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6312_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; 
v___x_6313_ = l_Lean_Int_mkInstMul;
v___x_6314_ = l_Lean_Int_mkType;
v___x_6315_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6316_ = l_Lean_mkAppB(v___x_6315_, v___x_6314_, v___x_6313_);
return v___x_6316_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6317_; 
v___x_6317_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6317_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6321_ = lean_box(0);
v___x_6322_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6323_ = l_Lean_Expr_const___override(v___x_6322_, v___x_6321_);
return v___x_6323_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6324_; 
v___x_6324_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6324_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6325_; lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; 
v___x_6325_ = l_Lean_Int_mkInstDiv;
v___x_6326_ = l_Lean_Int_mkType;
v___x_6327_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6328_ = l_Lean_mkAppB(v___x_6327_, v___x_6326_, v___x_6325_);
return v___x_6328_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6329_; 
v___x_6329_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6329_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6333_ = lean_box(0);
v___x_6334_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6335_ = l_Lean_Expr_const___override(v___x_6334_, v___x_6333_);
return v___x_6335_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6336_; 
v___x_6336_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6336_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; lean_object* v___x_6340_; 
v___x_6337_ = l_Lean_Int_mkInstMod;
v___x_6338_ = l_Lean_Int_mkType;
v___x_6339_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6340_ = l_Lean_mkAppB(v___x_6339_, v___x_6338_, v___x_6337_);
return v___x_6340_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6341_; 
v___x_6341_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6341_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; 
v___x_6346_ = lean_box(0);
v___x_6347_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6348_ = l_Lean_Expr_const___override(v___x_6347_, v___x_6346_);
return v___x_6348_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6349_; 
v___x_6349_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6349_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; 
v___x_6350_ = l_Lean_Int_mkInstPow;
v___x_6351_ = l_Lean_Int_mkType;
v___x_6352_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6353_ = l_Lean_mkAppB(v___x_6352_, v___x_6351_, v___x_6350_);
return v___x_6353_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6354_; 
v___x_6354_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6354_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; 
v___x_6355_ = l_Lean_Int_mkInstPowNat;
v___x_6356_ = l_Lean_Nat_mkType;
v___x_6357_ = l_Lean_Int_mkType;
v___x_6358_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6359_ = l_Lean_mkApp3(v___x_6358_, v___x_6357_, v___x_6356_, v___x_6355_);
return v___x_6359_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6360_; 
v___x_6360_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6360_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; 
v___x_6365_ = lean_box(0);
v___x_6366_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6367_ = l_Lean_Expr_const___override(v___x_6366_, v___x_6365_);
return v___x_6367_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6368_; 
v___x_6368_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6368_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; 
v___x_6373_ = lean_box(0);
v___x_6374_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6375_ = l_Lean_Expr_const___override(v___x_6374_, v___x_6373_);
return v___x_6375_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6376_; 
v___x_6376_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6376_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; 
v___x_6380_ = lean_box(0);
v___x_6381_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6382_ = l_Lean_Expr_const___override(v___x_6381_, v___x_6380_);
return v___x_6382_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6383_; 
v___x_6383_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6383_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; 
v___x_6384_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6385_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6386_ = l_Lean_Expr_const___override(v___x_6385_, v___x_6384_);
return v___x_6386_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; 
v___x_6387_ = l_Lean_Int_mkInstNeg;
v___x_6388_ = l_Lean_Int_mkType;
v___x_6389_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6390_ = l_Lean_mkAppB(v___x_6389_, v___x_6388_, v___x_6387_);
return v___x_6390_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6391_; 
v___x_6391_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6391_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; 
v___x_6392_ = l_Lean_Int_mkInstHAdd;
v___x_6393_ = l_Lean_Int_mkType;
v___x_6394_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6395_ = l_Lean_mkApp4(v___x_6394_, v___x_6393_, v___x_6393_, v___x_6393_, v___x_6392_);
return v___x_6395_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6396_; 
v___x_6396_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6396_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; 
v___x_6397_ = l_Lean_Int_mkInstHSub;
v___x_6398_ = l_Lean_Int_mkType;
v___x_6399_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6400_ = l_Lean_mkApp4(v___x_6399_, v___x_6398_, v___x_6398_, v___x_6398_, v___x_6397_);
return v___x_6400_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6401_; 
v___x_6401_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6401_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___x_6402_ = l_Lean_Int_mkInstHMul;
v___x_6403_ = l_Lean_Int_mkType;
v___x_6404_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6405_ = l_Lean_mkApp4(v___x_6404_, v___x_6403_, v___x_6403_, v___x_6403_, v___x_6402_);
return v___x_6405_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6406_; 
v___x_6406_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6406_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__0(void){
_start:
{
lean_object* v___x_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; 
v___x_6407_ = l_Lean_Int_mkInstHDiv;
v___x_6408_ = l_Lean_Int_mkType;
v___x_6409_ = lean_obj_once(&l_Lean_mkNatDiv___closed__3, &l_Lean_mkNatDiv___closed__3_once, _init_l_Lean_mkNatDiv___closed__3);
v___x_6410_ = l_Lean_mkApp4(v___x_6409_, v___x_6408_, v___x_6408_, v___x_6408_, v___x_6407_);
return v___x_6410_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6411_; 
v___x_6411_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__0, &l___private_Lean_Expr_0__Lean_intDivFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__0);
return v___x_6411_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__0(void){
_start:
{
lean_object* v___x_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; 
v___x_6412_ = l_Lean_Int_mkInstHMod;
v___x_6413_ = l_Lean_Int_mkType;
v___x_6414_ = lean_obj_once(&l_Lean_mkNatMod___closed__3, &l_Lean_mkNatMod___closed__3_once, _init_l_Lean_mkNatMod___closed__3);
v___x_6415_ = l_Lean_mkApp4(v___x_6414_, v___x_6413_, v___x_6413_, v___x_6413_, v___x_6412_);
return v___x_6415_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6416_; 
v___x_6416_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__0, &l___private_Lean_Expr_0__Lean_intModFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__0);
return v___x_6416_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6417_; lean_object* v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; 
v___x_6417_ = l_Lean_Int_mkInstHPow;
v___x_6418_ = l_Lean_Nat_mkType;
v___x_6419_ = l_Lean_Int_mkType;
v___x_6420_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6421_ = l_Lean_mkApp4(v___x_6420_, v___x_6419_, v___x_6418_, v___x_6419_, v___x_6417_);
return v___x_6421_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6422_; 
v___x_6422_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6422_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6428_; lean_object* v___x_6429_; lean_object* v___x_6430_; 
v___x_6428_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6429_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6430_ = l_Lean_Expr_const___override(v___x_6429_, v___x_6428_);
return v___x_6430_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; 
v___x_6431_ = l_Lean_Int_mkInstNatCast;
v___x_6432_ = l_Lean_Int_mkType;
v___x_6433_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6434_ = l_Lean_mkAppB(v___x_6433_, v___x_6432_, v___x_6431_);
return v___x_6434_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6435_; 
v___x_6435_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6435_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6436_){
_start:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; 
v___x_6437_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6438_ = l_Lean_Expr_app___override(v___x_6437_, v_a_6436_);
return v___x_6438_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6439_, lean_object* v_b_6440_){
_start:
{
lean_object* v___x_6441_; lean_object* v___x_6442_; 
v___x_6441_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6442_ = l_Lean_mkAppB(v___x_6441_, v_a_6439_, v_b_6440_);
return v___x_6442_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6443_, lean_object* v_b_6444_){
_start:
{
lean_object* v___x_6445_; lean_object* v___x_6446_; 
v___x_6445_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6446_ = l_Lean_mkAppB(v___x_6445_, v_a_6443_, v_b_6444_);
return v___x_6446_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6447_, lean_object* v_b_6448_){
_start:
{
lean_object* v___x_6449_; lean_object* v___x_6450_; 
v___x_6449_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6450_ = l_Lean_mkAppB(v___x_6449_, v_a_6447_, v_b_6448_);
return v___x_6450_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6451_, lean_object* v_b_6452_){
_start:
{
lean_object* v___x_6453_; lean_object* v___x_6454_; 
v___x_6453_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6454_ = l_Lean_mkAppB(v___x_6453_, v_a_6451_, v_b_6452_);
return v___x_6454_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6455_, lean_object* v_b_6456_){
_start:
{
lean_object* v___x_6457_; lean_object* v___x_6458_; 
v___x_6457_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6458_ = l_Lean_mkAppB(v___x_6457_, v_a_6455_, v_b_6456_);
return v___x_6458_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6459_){
_start:
{
lean_object* v___x_6460_; lean_object* v___x_6461_; 
v___x_6460_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6461_ = l_Lean_Expr_app___override(v___x_6460_, v_a_6459_);
return v___x_6461_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6462_, lean_object* v_b_6463_){
_start:
{
lean_object* v___x_6464_; lean_object* v___x_6465_; 
v___x_6464_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6465_ = l_Lean_mkAppB(v___x_6464_, v_a_6462_, v_b_6463_);
return v___x_6465_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; 
v___x_6466_ = l_Lean_Int_mkInstLE;
v___x_6467_ = l_Lean_Int_mkType;
v___x_6468_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6469_ = l_Lean_mkAppB(v___x_6468_, v___x_6467_, v___x_6466_);
return v___x_6469_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6470_; 
v___x_6470_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6470_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6471_, lean_object* v_b_6472_){
_start:
{
lean_object* v___x_6473_; lean_object* v___x_6474_; 
v___x_6473_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6474_ = l_Lean_mkAppB(v___x_6473_, v_a_6471_, v_b_6472_);
return v___x_6474_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; 
v___x_6480_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6481_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6482_ = l_Lean_Expr_const___override(v___x_6481_, v___x_6480_);
return v___x_6482_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; 
v___x_6483_ = l_Lean_Int_mkInstLT;
v___x_6484_ = l_Lean_Int_mkType;
v___x_6485_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6486_ = l_Lean_mkAppB(v___x_6485_, v___x_6484_, v___x_6483_);
return v___x_6486_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6487_; 
v___x_6487_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6487_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6488_, lean_object* v_b_6489_){
_start:
{
lean_object* v___x_6490_; lean_object* v___x_6491_; 
v___x_6490_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6491_ = l_Lean_mkAppB(v___x_6490_, v_a_6488_, v_b_6489_);
return v___x_6491_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; 
v___x_6492_ = l_Lean_Int_mkType;
v___x_6493_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6494_ = l_Lean_Expr_app___override(v___x_6493_, v___x_6492_);
return v___x_6494_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6495_; 
v___x_6495_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6496_, lean_object* v_b_6497_){
_start:
{
lean_object* v___x_6498_; lean_object* v___x_6499_; 
v___x_6498_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6499_ = l_Lean_mkAppB(v___x_6498_, v_a_6496_, v_b_6497_);
return v___x_6499_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; 
v___x_6505_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6506_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6507_ = l_Lean_Expr_const___override(v___x_6506_, v___x_6505_);
return v___x_6507_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; 
v___x_6512_ = lean_box(0);
v___x_6513_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6514_ = l_Lean_Expr_const___override(v___x_6513_, v___x_6512_);
return v___x_6514_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6515_, lean_object* v_b_6516_){
_start:
{
lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; 
v___x_6517_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6518_ = l_Lean_Int_mkType;
v___x_6519_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6520_ = l_Lean_mkApp4(v___x_6517_, v___x_6518_, v___x_6519_, v_a_6515_, v_b_6516_);
return v___x_6520_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6524_; lean_object* v___x_6525_; lean_object* v___x_6526_; 
v___x_6524_ = lean_box(0);
v___x_6525_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6526_ = l_Lean_Expr_const___override(v___x_6525_, v___x_6524_);
return v___x_6526_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6527_; lean_object* v___x_6528_; 
v___x_6527_ = lean_unsigned_to_nat(0u);
v___x_6528_ = lean_nat_to_int(v___x_6527_);
return v___x_6528_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6529_){
_start:
{
lean_object* v___x_6530_; lean_object* v_r_6531_; lean_object* v___x_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; lean_object* v_r_6536_; lean_object* v___x_6537_; uint8_t v___x_6538_; 
v___x_6530_ = lean_nat_abs(v_n_6529_);
v_r_6531_ = l_Lean_mkRawNatLit(v___x_6530_);
v___x_6532_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6533_ = l_Lean_Int_mkType;
v___x_6534_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6531_);
v___x_6535_ = l_Lean_Expr_app___override(v___x_6534_, v_r_6531_);
v_r_6536_ = l_Lean_mkApp3(v___x_6532_, v___x_6533_, v_r_6531_, v___x_6535_);
v___x_6537_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6538_ = lean_int_dec_lt(v_n_6529_, v___x_6537_);
if (v___x_6538_ == 0)
{
return v_r_6536_;
}
else
{
lean_object* v___x_6539_; 
v___x_6539_ = l_Lean_mkIntNeg(v_r_6536_);
return v___x_6539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6540_){
_start:
{
lean_object* v_res_6541_; 
v_res_6541_ = l_Lean_mkIntLit(v_n_6540_);
lean_dec(v_n_6540_);
return v_res_6541_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6546_; lean_object* v___x_6547_; 
v___x_6546_ = lean_box(0);
v___x_6547_ = l_Lean_Level_succ___override(v___x_6546_);
return v___x_6547_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; 
v___x_6548_ = lean_box(0);
v___x_6549_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6550_, 0, v___x_6549_);
lean_ctor_set(v___x_6550_, 1, v___x_6548_);
return v___x_6550_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; 
v___x_6551_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6552_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6553_ = l_Lean_Expr_const___override(v___x_6552_, v___x_6551_);
return v___x_6553_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6556_; lean_object* v___x_6557_; lean_object* v___x_6558_; 
v___x_6556_ = lean_box(0);
v___x_6557_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6558_ = l_Lean_Expr_const___override(v___x_6557_, v___x_6556_);
return v___x_6558_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; 
v___x_6559_ = lean_box(0);
v___x_6560_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6561_ = l_Lean_Expr_const___override(v___x_6560_, v___x_6559_);
return v___x_6561_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; 
v___x_6562_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6563_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6564_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6565_ = l_Lean_mkAppB(v___x_6564_, v___x_6563_, v___x_6562_);
return v___x_6565_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6566_; 
v___x_6566_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6566_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6569_; 
v___x_6567_ = lean_box(0);
v___x_6568_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__2));
v___x_6569_ = l_Lean_Expr_const___override(v___x_6568_, v___x_6567_);
return v___x_6569_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; 
v___x_6570_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6571_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6572_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6573_ = l_Lean_mkAppB(v___x_6572_, v___x_6571_, v___x_6570_);
return v___x_6573_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6574_; 
v___x_6574_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6574_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; 
v___x_6578_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6579_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6580_ = l_Lean_Expr_const___override(v___x_6579_, v___x_6578_);
return v___x_6580_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6581_; lean_object* v___x_6582_; lean_object* v___x_6583_; lean_object* v___x_6584_; 
v___x_6581_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6582_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6583_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6584_ = l_Lean_mkApp3(v___x_6583_, v___x_6582_, v___x_6581_, v___x_6581_);
return v___x_6584_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; 
v___x_6585_ = l_Lean_reflBoolTrue;
v___x_6586_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6587_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6588_ = l_Lean_mkAppB(v___x_6587_, v___x_6586_, v___x_6585_);
return v___x_6588_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6589_; 
v___x_6589_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6589_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; 
v___x_6590_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6591_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6592_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6593_ = l_Lean_mkApp3(v___x_6592_, v___x_6591_, v___x_6590_, v___x_6590_);
return v___x_6593_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; 
v___x_6594_ = l_Lean_reflBoolFalse;
v___x_6595_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6596_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6597_ = l_Lean_mkAppB(v___x_6596_, v___x_6595_, v___x_6594_);
return v___x_6597_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6598_; 
v___x_6598_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6598_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; 
v___x_6601_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6602_ = lean_unsigned_to_nat(9u);
v___x_6603_ = lean_unsigned_to_nat(2508u);
v___x_6604_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6605_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6606_ = l_mkPanicMessageWithDecl(v___x_6605_, v___x_6604_, v___x_6603_, v___x_6602_, v___x_6601_);
return v___x_6606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6607_, lean_object* v_declName_6608_){
_start:
{
switch(lean_obj_tag(v_e_6607_))
{
case 5:
{
lean_object* v_fn_6609_; lean_object* v_arg_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; 
v_fn_6609_ = lean_ctor_get(v_e_6607_, 0);
lean_inc_ref(v_fn_6609_);
v_arg_6610_ = lean_ctor_get(v_e_6607_, 1);
lean_inc_ref(v_arg_6610_);
lean_dec_ref_known(v_e_6607_, 2);
v___x_6611_ = l_Lean_Expr_replaceFn(v_fn_6609_, v_declName_6608_);
v___x_6612_ = l_Lean_Expr_app___override(v___x_6611_, v_arg_6610_);
return v___x_6612_;
}
case 4:
{
lean_object* v_us_6613_; lean_object* v___x_6614_; 
v_us_6613_ = lean_ctor_get(v_e_6607_, 1);
lean_inc(v_us_6613_);
lean_dec_ref_known(v_e_6607_, 2);
v___x_6614_ = l_Lean_Expr_const___override(v_declName_6608_, v_us_6613_);
return v___x_6614_;
}
default: 
{
lean_object* v___x_6615_; lean_object* v___x_6616_; 
lean_dec(v_declName_6608_);
lean_dec_ref(v_e_6607_);
v___x_6615_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6616_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6615_);
return v___x_6616_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin);
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
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_LBool(builtin);
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
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Lean_Data_LBool(uint8_t builtin);
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
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LBool(builtin);
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
