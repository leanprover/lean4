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
uint64_t lean_uint64_of_nat(lean_object*);
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
uint64_t lean_nat_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_natHash___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateAppN_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateAppN_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppN(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppN___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mapAppN___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mapAppN___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mapAppN___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mapAppN___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mapAppN(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Literal_natHash___boxed(lean_object* v_n_125_){
_start:
{
uint64_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = lean_nat_hash(v_n_125_);
lean_dec(v_n_125_);
v_r_127_ = lean_box_uint64(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v_val_129_; uint64_t v___x_130_; 
v_val_129_ = lean_ctor_get(v_x_128_, 0);
v___x_130_ = lean_nat_hash(v_val_129_);
return v___x_130_;
}
else
{
lean_object* v_val_131_; uint64_t v___x_132_; 
v_val_131_ = lean_ctor_get(v_x_128_, 0);
v___x_132_ = lean_string_hash(v_val_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object* v_x_133_){
_start:
{
uint64_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_Lean_Literal_hash(v_x_133_);
lean_dec_ref(v_x_133_);
v_r_135_ = lean_box_uint64(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_object* v_val_140_; lean_object* v_val_141_; uint8_t v___x_142_; 
v_val_140_ = lean_ctor_get(v_x_138_, 0);
v_val_141_ = lean_ctor_get(v_x_139_, 0);
v___x_142_ = lean_nat_dec_lt(v_val_140_, v_val_141_);
return v___x_142_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = 1;
return v___x_143_;
}
}
else
{
if (lean_obj_tag(v_x_139_) == 1)
{
lean_object* v_val_144_; lean_object* v_val_145_; uint8_t v___x_146_; 
v_val_144_ = lean_ctor_get(v_x_138_, 0);
v_val_145_ = lean_ctor_get(v_x_139_, 0);
v___x_146_ = lean_string_dec_lt(v_val_144_, v_val_145_);
return v___x_146_;
}
else
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Lean_Literal_lt(v_x_148_, v_x_149_);
lean_dec_ref(v_x_149_);
lean_dec_ref(v_x_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
static lean_object* _init_l_Lean_instLTLiteral(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_box(0);
return v___x_152_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteral(lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_Literal_lt(v_a_153_, v_b_154_);
return v___x_155_;
}
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
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl(uint8_t v_x_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(v_x_160_);
v___x_162_ = lean_obj_tag_nat(v___x_161_);
lean_dec(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl___boxed(lean_object* v_x_163_){
_start:
{
uint8_t v_x_4__boxed_164_; lean_object* v_res_165_; 
v_x_4__boxed_164_ = lean_unbox(v_x_163_);
v_res_165_ = l_Lean_BinderInfo_ctorIdx___impl(v_x_4__boxed_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg(lean_object* v_k_166_){
_start:
{
lean_inc(v_k_166_);
return v_k_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg___boxed(lean_object* v_k_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_BinderInfo_ctorElim___redArg(v_k_167_);
lean_dec(v_k_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim(lean_object* v_motive_169_, lean_object* v_ctorIdx_170_, uint8_t v_t_171_, lean_object* v_h_172_, lean_object* v_k_173_){
_start:
{
lean_inc(v_k_173_);
return v_k_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___boxed(lean_object* v_motive_174_, lean_object* v_ctorIdx_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_k_178_){
_start:
{
uint8_t v_t_boxed_179_; lean_object* v_res_180_; 
v_t_boxed_179_ = lean_unbox(v_t_176_);
v_res_180_ = l_Lean_BinderInfo_ctorElim(v_motive_174_, v_ctorIdx_175_, v_t_boxed_179_, v_h_177_, v_k_178_);
lean_dec(v_k_178_);
lean_dec(v_ctorIdx_175_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg(lean_object* v_default_181_){
_start:
{
lean_inc(v_default_181_);
return v_default_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg___boxed(lean_object* v_default_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_BinderInfo_default_elim___redArg(v_default_182_);
lean_dec(v_default_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim(lean_object* v_motive_184_, uint8_t v_t_185_, lean_object* v_h_186_, lean_object* v_default_187_){
_start:
{
lean_inc(v_default_187_);
return v_default_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___boxed(lean_object* v_motive_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_default_191_){
_start:
{
uint8_t v_t_boxed_192_; lean_object* v_res_193_; 
v_t_boxed_192_ = lean_unbox(v_t_189_);
v_res_193_ = l_Lean_BinderInfo_default_elim(v_motive_188_, v_t_boxed_192_, v_h_190_, v_default_191_);
lean_dec(v_default_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg(lean_object* v_implicit_194_){
_start:
{
lean_inc(v_implicit_194_);
return v_implicit_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg___boxed(lean_object* v_implicit_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_BinderInfo_implicit_elim___redArg(v_implicit_195_);
lean_dec(v_implicit_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim(lean_object* v_motive_197_, uint8_t v_t_198_, lean_object* v_h_199_, lean_object* v_implicit_200_){
_start:
{
lean_inc(v_implicit_200_);
return v_implicit_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___boxed(lean_object* v_motive_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_implicit_204_){
_start:
{
uint8_t v_t_boxed_205_; lean_object* v_res_206_; 
v_t_boxed_205_ = lean_unbox(v_t_202_);
v_res_206_ = l_Lean_BinderInfo_implicit_elim(v_motive_201_, v_t_boxed_205_, v_h_203_, v_implicit_204_);
lean_dec(v_implicit_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg(lean_object* v_strictImplicit_207_){
_start:
{
lean_inc(v_strictImplicit_207_);
return v_strictImplicit_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg___boxed(lean_object* v_strictImplicit_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_BinderInfo_strictImplicit_elim___redArg(v_strictImplicit_208_);
lean_dec(v_strictImplicit_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim(lean_object* v_motive_210_, uint8_t v_t_211_, lean_object* v_h_212_, lean_object* v_strictImplicit_213_){
_start:
{
lean_inc(v_strictImplicit_213_);
return v_strictImplicit_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___boxed(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_strictImplicit_217_){
_start:
{
uint8_t v_t_boxed_218_; lean_object* v_res_219_; 
v_t_boxed_218_ = lean_unbox(v_t_215_);
v_res_219_ = l_Lean_BinderInfo_strictImplicit_elim(v_motive_214_, v_t_boxed_218_, v_h_216_, v_strictImplicit_217_);
lean_dec(v_strictImplicit_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg(lean_object* v_instImplicit_220_){
_start:
{
lean_inc(v_instImplicit_220_);
return v_instImplicit_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg___boxed(lean_object* v_instImplicit_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_BinderInfo_instImplicit_elim___redArg(v_instImplicit_221_);
lean_dec(v_instImplicit_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim(lean_object* v_motive_223_, uint8_t v_t_224_, lean_object* v_h_225_, lean_object* v_instImplicit_226_){
_start:
{
lean_inc(v_instImplicit_226_);
return v_instImplicit_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___boxed(lean_object* v_motive_227_, lean_object* v_t_228_, lean_object* v_h_229_, lean_object* v_instImplicit_230_){
_start:
{
uint8_t v_t_boxed_231_; lean_object* v_res_232_; 
v_t_boxed_231_ = lean_unbox(v_t_228_);
v_res_232_ = l_Lean_BinderInfo_instImplicit_elim(v_motive_227_, v_t_boxed_231_, v_h_229_, v_instImplicit_230_);
lean_dec(v_instImplicit_230_);
return v_res_232_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo_default(void){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo(void){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = 0;
return v___x_234_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t v_x_235_, uint8_t v_y_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_237_ = lean_box(v_x_235_);
v___x_238_ = lean_obj_tag_nat(v___x_237_);
lean_dec(v___x_237_);
v___x_239_ = lean_box(v_y_236_);
v___x_240_ = lean_obj_tag_nat(v___x_239_);
lean_dec(v___x_239_);
v___x_241_ = lean_nat_dec_eq(v___x_238_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo_beq___boxed(lean_object* v_x_242_, lean_object* v_y_243_){
_start:
{
uint8_t v_x_24__boxed_244_; uint8_t v_y_25__boxed_245_; uint8_t v_res_246_; lean_object* v_r_247_; 
v_x_24__boxed_244_ = lean_unbox(v_x_242_);
v_y_25__boxed_245_ = lean_unbox(v_y_243_);
v_res_246_ = l_Lean_instBEqBinderInfo_beq(v_x_24__boxed_244_, v_y_25__boxed_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr(uint8_t v_x_262_, lean_object* v_prec_263_){
_start:
{
lean_object* v___y_265_; lean_object* v___y_272_; lean_object* v___y_279_; lean_object* v___y_286_; 
switch(v_x_262_)
{
case 0:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(1024u);
v___x_293_ = lean_nat_dec_le(v___x_292_, v_prec_263_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_265_ = v___x_294_;
goto v___jp_264_;
}
else
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_265_ = v___x_295_;
goto v___jp_264_;
}
}
case 1:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(1024u);
v___x_297_ = lean_nat_dec_le(v___x_296_, v_prec_263_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_272_ = v___x_298_;
goto v___jp_271_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_272_ = v___x_299_;
goto v___jp_271_;
}
}
case 2:
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(1024u);
v___x_301_ = lean_nat_dec_le(v___x_300_, v_prec_263_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_279_ = v___x_302_;
goto v___jp_278_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_279_ = v___x_303_;
goto v___jp_278_;
}
}
default: 
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(1024u);
v___x_305_ = lean_nat_dec_le(v___x_304_, v_prec_263_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_286_ = v___x_306_;
goto v___jp_285_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_286_ = v___x_307_;
goto v___jp_285_;
}
}
}
v___jp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_266_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__1));
lean_inc(v___y_265_);
v___x_267_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_267_, 0, v___y_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = 0;
v___x_269_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*1, v___x_268_);
v___x_270_ = l_Repr_addAppParen(v___x_269_, v_prec_263_);
return v___x_270_;
}
v___jp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_273_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__3));
lean_inc(v___y_272_);
v___x_274_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_274_, 0, v___y_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = 0;
v___x_276_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v___x_275_);
v___x_277_ = l_Repr_addAppParen(v___x_276_, v_prec_263_);
return v___x_277_;
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_280_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__5));
lean_inc(v___y_279_);
v___x_281_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_281_, 0, v___y_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = 0;
v___x_283_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*1, v___x_282_);
v___x_284_ = l_Repr_addAppParen(v___x_283_, v_prec_263_);
return v___x_284_;
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_287_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__7));
lean_inc(v___y_286_);
v___x_288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_288_, 0, v___y_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = 0;
v___x_290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*1, v___x_289_);
v___x_291_ = l_Repr_addAppParen(v___x_290_, v_prec_263_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr___boxed(lean_object* v_x_308_, lean_object* v_prec_309_){
_start:
{
uint8_t v_x_221__boxed_310_; lean_object* v_res_311_; 
v_x_221__boxed_310_ = lean_unbox(v_x_308_);
v_res_311_ = l_Lean_instReprBinderInfo_repr(v_x_221__boxed_310_, v_prec_309_);
lean_dec(v_prec_309_);
return v_res_311_;
}
}
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t v_x_314_){
_start:
{
switch(v_x_314_)
{
case 0:
{
uint64_t v___x_315_; 
v___x_315_ = 947ULL;
return v___x_315_;
}
case 1:
{
uint64_t v___x_316_; 
v___x_316_ = 1019ULL;
return v___x_316_;
}
case 2:
{
uint64_t v___x_317_; 
v___x_317_ = 1087ULL;
return v___x_317_;
}
default: 
{
uint64_t v___x_318_; 
v___x_318_ = 1153ULL;
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object* v_x_319_){
_start:
{
uint8_t v_x_52__boxed_320_; uint64_t v_res_321_; lean_object* v_r_322_; 
v_x_52__boxed_320_ = lean_unbox(v_x_319_);
v_res_321_ = l_Lean_BinderInfo_hash(v_x_52__boxed_320_);
v_r_322_ = lean_box_uint64(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t v_x_323_){
_start:
{
switch(v_x_323_)
{
case 1:
{
uint8_t v___x_324_; 
v___x_324_ = 0;
return v___x_324_;
}
case 2:
{
uint8_t v___x_325_; 
v___x_325_ = 0;
return v___x_325_;
}
case 3:
{
uint8_t v___x_326_; 
v___x_326_ = 0;
return v___x_326_;
}
default: 
{
uint8_t v___x_327_; 
v___x_327_ = 1;
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object* v_x_328_){
_start:
{
uint8_t v_x_27__boxed_329_; uint8_t v_res_330_; lean_object* v_r_331_; 
v_x_27__boxed_329_ = lean_unbox(v_x_328_);
v_res_330_ = l_Lean_BinderInfo_isExplicit(v_x_27__boxed_329_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t v_x_334_){
_start:
{
if (v_x_334_ == 3)
{
uint8_t v___x_335_; 
v___x_335_ = 1;
return v___x_335_;
}
else
{
uint8_t v___x_336_; 
v___x_336_ = 0;
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object* v_x_337_){
_start:
{
uint8_t v_x_17__boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v_x_17__boxed_338_ = lean_unbox(v_x_337_);
v_res_339_ = l_Lean_BinderInfo_isInstImplicit(v_x_17__boxed_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t v_x_341_){
_start:
{
if (v_x_341_ == 1)
{
uint8_t v___x_342_; 
v___x_342_ = 1;
return v___x_342_;
}
else
{
uint8_t v___x_343_; 
v___x_343_ = 0;
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object* v_x_344_){
_start:
{
uint8_t v_x_17__boxed_345_; uint8_t v_res_346_; lean_object* v_r_347_; 
v_x_17__boxed_345_ = lean_unbox(v_x_344_);
v_res_346_ = l_Lean_BinderInfo_isImplicit(v_x_17__boxed_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t v_x_348_){
_start:
{
if (v_x_348_ == 2)
{
uint8_t v___x_349_; 
v___x_349_ = 1;
return v___x_349_;
}
else
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object* v_x_351_){
_start:
{
uint8_t v_x_17__boxed_352_; uint8_t v_res_353_; lean_object* v_r_354_; 
v_x_17__boxed_352_ = lean_unbox(v_x_351_);
v_res_353_ = l_Lean_BinderInfo_isStrictImplicit(v_x_17__boxed_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
static lean_object* _init_l_Lean_MData_empty(void){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_box(0);
return v___x_355_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1___aux__1(void){
_start:
{
uint64_t v___x_356_; 
v___x_356_ = 0ULL;
return v___x_356_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1(void){
_start:
{
uint64_t v___x_357_; 
v___x_357_ = 0ULL;
return v___x_357_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_hash(uint64_t v_c_358_){
_start:
{
uint32_t v___x_359_; 
v___x_359_ = lean_uint64_to_uint32(v_c_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* v_c_360_){
_start:
{
uint64_t v_c_boxed_361_; uint32_t v_res_362_; lean_object* v_r_363_; 
v_c_boxed_361_ = lean_unbox_uint64(v_c_360_);
lean_dec_ref(v_c_360_);
v_res_362_ = l_Lean_Expr_Data_hash(v_c_boxed_361_);
v_r_363_ = lean_box_uint32(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t v_c_366_){
_start:
{
uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint8_t v___x_371_; 
v___x_367_ = 32ULL;
v___x_368_ = lean_uint64_shift_right(v_c_366_, v___x_367_);
v___x_369_ = 255ULL;
v___x_370_ = lean_uint64_land(v___x_368_, v___x_369_);
v___x_371_ = lean_uint64_to_uint8(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* v_c_372_){
_start:
{
uint64_t v_c_boxed_373_; uint8_t v_res_374_; lean_object* v_r_375_; 
v_c_boxed_373_ = lean_unbox_uint64(v_c_372_);
lean_dec_ref(v_c_372_);
v_res_374_ = l_Lean_Expr_Data_approxDepth(v_c_boxed_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t v_c_376_){
_start:
{
uint64_t v___x_377_; uint64_t v___x_378_; uint32_t v___x_379_; 
v___x_377_ = 44ULL;
v___x_378_ = lean_uint64_shift_right(v_c_376_, v___x_377_);
v___x_379_ = lean_uint64_to_uint32(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* v_c_380_){
_start:
{
uint64_t v_c_boxed_381_; uint32_t v_res_382_; lean_object* v_r_383_; 
v_c_boxed_381_ = lean_unbox_uint64(v_c_380_);
lean_dec_ref(v_c_380_);
v_res_382_ = l_Lean_Expr_Data_looseBVarRange(v_c_boxed_381_);
v_r_383_ = lean_box_uint32(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t v_c_384_){
_start:
{
uint64_t v___x_385_; uint64_t v___x_386_; uint64_t v___x_387_; uint64_t v___x_388_; uint8_t v___x_389_; 
v___x_385_ = 40ULL;
v___x_386_ = lean_uint64_shift_right(v_c_384_, v___x_385_);
v___x_387_ = 1ULL;
v___x_388_ = lean_uint64_land(v___x_386_, v___x_387_);
v___x_389_ = lean_uint64_dec_eq(v___x_388_, v___x_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* v_c_390_){
_start:
{
uint64_t v_c_boxed_391_; uint8_t v_res_392_; lean_object* v_r_393_; 
v_c_boxed_391_ = lean_unbox_uint64(v_c_390_);
lean_dec_ref(v_c_390_);
v_res_392_ = l_Lean_Expr_Data_hasFVar(v_c_boxed_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t v_c_394_){
_start:
{
uint64_t v___x_395_; uint64_t v___x_396_; uint64_t v___x_397_; uint64_t v___x_398_; uint8_t v___x_399_; 
v___x_395_ = 41ULL;
v___x_396_ = lean_uint64_shift_right(v_c_394_, v___x_395_);
v___x_397_ = 1ULL;
v___x_398_ = lean_uint64_land(v___x_396_, v___x_397_);
v___x_399_ = lean_uint64_dec_eq(v___x_398_, v___x_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* v_c_400_){
_start:
{
uint64_t v_c_boxed_401_; uint8_t v_res_402_; lean_object* v_r_403_; 
v_c_boxed_401_ = lean_unbox_uint64(v_c_400_);
lean_dec_ref(v_c_400_);
v_res_402_ = l_Lean_Expr_Data_hasExprMVar(v_c_boxed_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t v_c_404_){
_start:
{
uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint8_t v___x_409_; 
v___x_405_ = 42ULL;
v___x_406_ = lean_uint64_shift_right(v_c_404_, v___x_405_);
v___x_407_ = 1ULL;
v___x_408_ = lean_uint64_land(v___x_406_, v___x_407_);
v___x_409_ = lean_uint64_dec_eq(v___x_408_, v___x_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* v_c_410_){
_start:
{
uint64_t v_c_boxed_411_; uint8_t v_res_412_; lean_object* v_r_413_; 
v_c_boxed_411_ = lean_unbox_uint64(v_c_410_);
lean_dec_ref(v_c_410_);
v_res_412_ = l_Lean_Expr_Data_hasLevelMVar(v_c_boxed_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t v_c_414_){
_start:
{
uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v___x_418_; uint8_t v___x_419_; 
v___x_415_ = 43ULL;
v___x_416_ = lean_uint64_shift_right(v_c_414_, v___x_415_);
v___x_417_ = 1ULL;
v___x_418_ = lean_uint64_land(v___x_416_, v___x_417_);
v___x_419_ = lean_uint64_dec_eq(v___x_418_, v___x_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* v_c_420_){
_start:
{
uint64_t v_c_boxed_421_; uint8_t v_res_422_; lean_object* v_r_423_; 
v_c_boxed_421_ = lean_unbox_uint64(v_c_420_);
lean_dec_ref(v_c_420_);
v_res_422_ = l_Lean_Expr_Data_hasLevelParam(v_c_boxed_421_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_425_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_426_; uint64_t v_res_427_; lean_object* v_r_428_; 
v_a_00___x40___internal___hyg_1__boxed_426_ = lean_unbox(v_a_00___x40___internal___hyg_425_);
v_res_427_ = lean_uint8_to_uint64(v_a_00___x40___internal___hyg_1__boxed_426_);
v_r_428_ = lean_box_uint64(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* v_h_436_, lean_object* v_looseBVarRange_437_, lean_object* v_approxDepth_438_, lean_object* v_hasFVar_439_, lean_object* v_hasExprMVar_440_, lean_object* v_hasLevelMVar_441_, lean_object* v_hasLevelParam_442_){
_start:
{
uint32_t v_h_boxed_443_; uint32_t v_approxDepth_boxed_444_; uint8_t v_hasFVar_boxed_445_; uint8_t v_hasExprMVar_boxed_446_; uint8_t v_hasLevelMVar_boxed_447_; uint8_t v_hasLevelParam_boxed_448_; uint64_t v_res_449_; lean_object* v_r_450_; 
v_h_boxed_443_ = lean_unbox_uint32(v_h_436_);
lean_dec(v_h_436_);
v_approxDepth_boxed_444_ = lean_unbox_uint32(v_approxDepth_438_);
lean_dec(v_approxDepth_438_);
v_hasFVar_boxed_445_ = lean_unbox(v_hasFVar_439_);
v_hasExprMVar_boxed_446_ = lean_unbox(v_hasExprMVar_440_);
v_hasLevelMVar_boxed_447_ = lean_unbox(v_hasLevelMVar_441_);
v_hasLevelParam_boxed_448_ = lean_unbox(v_hasLevelParam_442_);
v_res_449_ = lean_expr_mk_data(v_h_boxed_443_, v_looseBVarRange_437_, v_approxDepth_boxed_444_, v_hasFVar_boxed_445_, v_hasExprMVar_boxed_446_, v_hasLevelMVar_boxed_447_, v_hasLevelParam_boxed_448_);
v_r_450_ = lean_box_uint64(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* v_fData_453_, lean_object* v_aData_454_){
_start:
{
uint64_t v_fData_boxed_455_; uint64_t v_aData_boxed_456_; uint64_t v_res_457_; lean_object* v_r_458_; 
v_fData_boxed_455_ = lean_unbox_uint64(v_fData_453_);
lean_dec_ref(v_fData_453_);
v_aData_boxed_456_ = lean_unbox_uint64(v_aData_454_);
lean_dec_ref(v_aData_454_);
v_res_457_ = lean_expr_mk_app_data(v_fData_boxed_455_, v_aData_boxed_456_);
v_r_458_ = lean_box_uint64(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint32_t v_h_459_, lean_object* v_looseBVarRange_460_, uint32_t v_approxDepth_461_, uint8_t v_hasFVar_462_, uint8_t v_hasExprMVar_463_, uint8_t v_hasLevelMVar_464_, uint8_t v_hasLevelParam_465_){
_start:
{
uint64_t v___x_466_; 
v___x_466_ = lean_expr_mk_data(v_h_459_, v_looseBVarRange_460_, v_approxDepth_461_, v_hasFVar_462_, v_hasExprMVar_463_, v_hasLevelMVar_464_, v_hasLevelParam_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* v_h_467_, lean_object* v_looseBVarRange_468_, lean_object* v_approxDepth_469_, lean_object* v_hasFVar_470_, lean_object* v_hasExprMVar_471_, lean_object* v_hasLevelMVar_472_, lean_object* v_hasLevelParam_473_){
_start:
{
uint32_t v_h_boxed_474_; uint32_t v_approxDepth_boxed_475_; uint8_t v_hasFVar_boxed_476_; uint8_t v_hasExprMVar_boxed_477_; uint8_t v_hasLevelMVar_boxed_478_; uint8_t v_hasLevelParam_boxed_479_; uint64_t v_res_480_; lean_object* v_r_481_; 
v_h_boxed_474_ = lean_unbox_uint32(v_h_467_);
lean_dec(v_h_467_);
v_approxDepth_boxed_475_ = lean_unbox_uint32(v_approxDepth_469_);
lean_dec(v_approxDepth_469_);
v_hasFVar_boxed_476_ = lean_unbox(v_hasFVar_470_);
v_hasExprMVar_boxed_477_ = lean_unbox(v_hasExprMVar_471_);
v_hasLevelMVar_boxed_478_ = lean_unbox(v_hasLevelMVar_472_);
v_hasLevelParam_boxed_479_ = lean_unbox(v_hasLevelParam_473_);
v_res_480_ = l_Lean_Expr_mkDataForBinder(v_h_boxed_474_, v_looseBVarRange_468_, v_approxDepth_boxed_475_, v_hasFVar_boxed_476_, v_hasExprMVar_boxed_477_, v_hasLevelMVar_boxed_478_, v_hasLevelParam_boxed_479_);
v_r_481_ = lean_box_uint64(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint32_t v_h_482_, lean_object* v_looseBVarRange_483_, uint32_t v_approxDepth_484_, uint8_t v_hasFVar_485_, uint8_t v_hasExprMVar_486_, uint8_t v_hasLevelMVar_487_, uint8_t v_hasLevelParam_488_){
_start:
{
uint64_t v___x_489_; 
v___x_489_ = lean_expr_mk_data(v_h_482_, v_looseBVarRange_483_, v_approxDepth_484_, v_hasFVar_485_, v_hasExprMVar_486_, v_hasLevelMVar_487_, v_hasLevelParam_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* v_h_490_, lean_object* v_looseBVarRange_491_, lean_object* v_approxDepth_492_, lean_object* v_hasFVar_493_, lean_object* v_hasExprMVar_494_, lean_object* v_hasLevelMVar_495_, lean_object* v_hasLevelParam_496_){
_start:
{
uint32_t v_h_boxed_497_; uint32_t v_approxDepth_boxed_498_; uint8_t v_hasFVar_boxed_499_; uint8_t v_hasExprMVar_boxed_500_; uint8_t v_hasLevelMVar_boxed_501_; uint8_t v_hasLevelParam_boxed_502_; uint64_t v_res_503_; lean_object* v_r_504_; 
v_h_boxed_497_ = lean_unbox_uint32(v_h_490_);
lean_dec(v_h_490_);
v_approxDepth_boxed_498_ = lean_unbox_uint32(v_approxDepth_492_);
lean_dec(v_approxDepth_492_);
v_hasFVar_boxed_499_ = lean_unbox(v_hasFVar_493_);
v_hasExprMVar_boxed_500_ = lean_unbox(v_hasExprMVar_494_);
v_hasLevelMVar_boxed_501_ = lean_unbox(v_hasLevelMVar_495_);
v_hasLevelParam_boxed_502_ = lean_unbox(v_hasLevelParam_496_);
v_res_503_ = l_Lean_Expr_mkDataForLet(v_h_boxed_497_, v_looseBVarRange_491_, v_approxDepth_boxed_498_, v_hasFVar_boxed_499_, v_hasExprMVar_boxed_500_, v_hasLevelMVar_boxed_501_, v_hasLevelParam_boxed_502_);
v_r_504_ = lean_box_uint64(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t v_v_513_, lean_object* v_prec_514_){
_start:
{
lean_object* v_r_516_; lean_object* v_r_520_; lean_object* v_r_529_; lean_object* v_r_538_; lean_object* v_r_547_; lean_object* v___x_558_; uint32_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_r_562_; uint32_t v___x_563_; uint32_t v___x_564_; uint8_t v___x_565_; 
v___x_558_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__6));
v___x_559_ = lean_uint64_to_uint32(v_v_513_);
v___x_560_ = lean_uint32_to_nat(v___x_559_);
v___x_561_ = l_Nat_reprFast(v___x_560_);
v_r_562_ = lean_string_append(v___x_558_, v___x_561_);
lean_dec_ref(v___x_561_);
v___x_563_ = l_Lean_Expr_Data_looseBVarRange(v_v_513_);
v___x_564_ = 0;
v___x_565_ = lean_uint32_dec_eq(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_r_572_; 
v___x_566_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__7));
v___x_567_ = lean_string_append(v_r_562_, v___x_566_);
v___x_568_ = lean_uint32_to_nat(v___x_563_);
v___x_569_ = l_Nat_reprFast(v___x_568_);
v___x_570_ = lean_string_append(v___x_567_, v___x_569_);
lean_dec_ref(v___x_569_);
v___x_571_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_572_ = lean_string_append(v___x_570_, v___x_571_);
v_r_547_ = v_r_572_;
goto v___jp_546_;
}
else
{
v_r_547_ = v_r_562_;
goto v___jp_546_;
}
v___jp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_517_, 0, v_r_516_);
v___x_518_ = l_Repr_addAppParen(v___x_517_, v_prec_514_);
return v___x_518_;
}
v___jp_519_:
{
uint8_t v___x_521_; 
v___x_521_ = l_Lean_Expr_Data_hasLevelMVar(v_v_513_);
if (v___x_521_ == 0)
{
v_r_516_ = v_r_520_;
goto v___jp_515_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_r_527_; 
v___x_522_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v___x_523_ = lean_string_append(v_r_520_, v___x_522_);
v___x_524_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_525_ = lean_string_append(v___x_523_, v___x_524_);
v___x_526_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_527_ = lean_string_append(v___x_525_, v___x_526_);
v_r_516_ = v_r_527_;
goto v___jp_515_;
}
}
v___jp_528_:
{
uint8_t v___x_530_; 
v___x_530_ = l_Lean_Expr_Data_hasExprMVar(v_v_513_);
if (v___x_530_ == 0)
{
v_r_520_ = v_r_529_;
goto v___jp_519_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_r_536_; 
v___x_531_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___x_532_ = lean_string_append(v_r_529_, v___x_531_);
v___x_533_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_534_ = lean_string_append(v___x_532_, v___x_533_);
v___x_535_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_536_ = lean_string_append(v___x_534_, v___x_535_);
v_r_520_ = v_r_536_;
goto v___jp_519_;
}
}
v___jp_537_:
{
uint8_t v___x_539_; 
v___x_539_ = l_Lean_Expr_Data_hasFVar(v_v_513_);
if (v___x_539_ == 0)
{
v_r_529_ = v_r_538_;
goto v___jp_528_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_r_545_; 
v___x_540_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__4));
v___x_541_ = lean_string_append(v_r_538_, v___x_540_);
v___x_542_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
v___x_544_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_545_ = lean_string_append(v___x_543_, v___x_544_);
v_r_529_ = v_r_545_;
goto v___jp_528_;
}
}
v___jp_546_:
{
uint8_t v___x_548_; uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_548_ = l_Lean_Expr_Data_approxDepth(v_v_513_);
v___x_549_ = 0;
v___x_550_ = lean_uint8_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v_r_557_; 
v___x_551_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__5));
v___x_552_ = lean_string_append(v_r_547_, v___x_551_);
v___x_553_ = lean_uint8_to_nat(v___x_548_);
v___x_554_ = l_Nat_reprFast(v___x_553_);
v___x_555_ = lean_string_append(v___x_552_, v___x_554_);
lean_dec_ref(v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_557_ = lean_string_append(v___x_555_, v___x_556_);
v_r_538_ = v_r_557_;
goto v___jp_537_;
}
else
{
v_r_538_ = v_r_547_;
goto v___jp_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* v_v_573_, lean_object* v_prec_574_){
_start:
{
uint64_t v_v_boxed_575_; lean_object* v_res_576_; 
v_v_boxed_575_ = lean_unbox_uint64(v_v_573_);
lean_dec_ref(v_v_573_);
v_res_576_ = l_Lean_instReprData__1___lam__0(v_v_boxed_575_, v_prec_574_);
lean_dec(v_prec_574_);
return v_res_576_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId_default(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lean_box(0);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId(void){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = lean_box(0);
return v___x_580_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
uint8_t v___x_583_; 
v___x_583_ = lean_name_eq(v_x_581_, v_x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
uint8_t v_res_586_; lean_object* v_r_587_; 
v_res_586_ = l_Lean_instBEqFVarId_beq(v_x_584_, v_x_585_);
lean_dec(v_x_585_);
lean_dec(v_x_584_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_590_){
_start:
{
uint64_t v___x_591_; 
v___x_591_ = 0ULL;
if (lean_obj_tag(v_x_590_) == 0)
{
uint64_t v___x_592_; 
v___x_592_ = 8934034000889494153ULL;
return v___x_592_;
}
else
{
uint64_t v_hash_593_; uint64_t v___x_594_; 
v_hash_593_ = lean_ctor_get_uint64(v_x_590_, sizeof(void*)*2);
v___x_594_ = lean_uint64_mix_hash(v___x_591_, v_hash_593_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_595_){
_start:
{
uint64_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l_Lean_instHashableFVarId_hash(v_x_595_);
lean_dec(v_x_595_);
v_r_597_ = lean_box_uint64(v_res_596_);
return v_r_597_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = lean_box(1);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_box(1);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = lean_box(1);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet(void){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = lean_box(1);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object* v_e_607_){
_start:
{
lean_object* v___f_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___f_608_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_609_ = lean_box(1);
lean_inc(v_e_607_);
v___x_610_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_608_, v_e_607_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_box(0);
v___x_612_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_608_, v_e_607_, v___x_611_, v___x_609_);
return v___x_612_;
}
else
{
lean_dec(v_e_607_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object* v_k_613_, lean_object* v_v_614_, lean_object* v_t_615_){
_start:
{
if (lean_obj_tag(v_t_615_) == 0)
{
lean_object* v_size_616_; lean_object* v_k_617_; lean_object* v_v_618_; lean_object* v_l_619_; lean_object* v_r_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_900_; 
v_size_616_ = lean_ctor_get(v_t_615_, 0);
v_k_617_ = lean_ctor_get(v_t_615_, 1);
v_v_618_ = lean_ctor_get(v_t_615_, 2);
v_l_619_ = lean_ctor_get(v_t_615_, 3);
v_r_620_ = lean_ctor_get(v_t_615_, 4);
v_isSharedCheck_900_ = !lean_is_exclusive(v_t_615_);
if (v_isSharedCheck_900_ == 0)
{
v___x_622_ = v_t_615_;
v_isShared_623_ = v_isSharedCheck_900_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_r_620_);
lean_inc(v_l_619_);
lean_inc(v_v_618_);
lean_inc(v_k_617_);
lean_inc(v_size_616_);
lean_dec(v_t_615_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_900_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint8_t v___x_624_; 
v___x_624_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_613_, v_k_617_);
switch(v___x_624_)
{
case 0:
{
lean_object* v_impl_625_; lean_object* v___x_626_; 
lean_dec(v_size_616_);
v_impl_625_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_613_, v_v_614_, v_l_619_);
v___x_626_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_620_) == 0)
{
lean_object* v_size_627_; lean_object* v_size_628_; lean_object* v_k_629_; lean_object* v_v_630_; lean_object* v_l_631_; lean_object* v_r_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_size_627_ = lean_ctor_get(v_r_620_, 0);
v_size_628_ = lean_ctor_get(v_impl_625_, 0);
v_k_629_ = lean_ctor_get(v_impl_625_, 1);
v_v_630_ = lean_ctor_get(v_impl_625_, 2);
v_l_631_ = lean_ctor_get(v_impl_625_, 3);
v_r_632_ = lean_ctor_get(v_impl_625_, 4);
lean_inc(v_r_632_);
v___x_633_ = lean_unsigned_to_nat(3u);
v___x_634_ = lean_nat_mul(v___x_633_, v_size_627_);
v___x_635_ = lean_nat_dec_lt(v___x_634_, v_size_628_);
lean_dec(v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
lean_dec(v_r_632_);
v___x_636_ = lean_nat_add(v___x_626_, v_size_628_);
v___x_637_ = lean_nat_add(v___x_636_, v_size_627_);
lean_dec(v___x_636_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 3, v_impl_625_);
lean_ctor_set(v___x_622_, 0, v___x_637_);
v___x_639_ = v___x_622_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v_impl_625_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v_r_620_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_706_; 
lean_inc(v_l_631_);
lean_inc(v_v_630_);
lean_inc(v_k_629_);
lean_inc(v_size_628_);
v_isSharedCheck_706_ = !lean_is_exclusive(v_impl_625_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; 
v_unused_707_ = lean_ctor_get(v_impl_625_, 4);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_impl_625_, 3);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_impl_625_, 2);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_impl_625_, 1);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_impl_625_, 0);
lean_dec(v_unused_711_);
v___x_642_ = v_impl_625_;
v_isShared_643_ = v_isSharedCheck_706_;
goto v_resetjp_641_;
}
else
{
lean_dec(v_impl_625_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_706_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_size_644_; lean_object* v_size_645_; lean_object* v_k_646_; lean_object* v_v_647_; lean_object* v_l_648_; lean_object* v_r_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_size_644_ = lean_ctor_get(v_l_631_, 0);
v_size_645_ = lean_ctor_get(v_r_632_, 0);
v_k_646_ = lean_ctor_get(v_r_632_, 1);
v_v_647_ = lean_ctor_get(v_r_632_, 2);
v_l_648_ = lean_ctor_get(v_r_632_, 3);
v_r_649_ = lean_ctor_get(v_r_632_, 4);
v___x_650_ = lean_unsigned_to_nat(2u);
v___x_651_ = lean_nat_mul(v___x_650_, v_size_644_);
v___x_652_ = lean_nat_dec_lt(v_size_645_, v___x_651_);
lean_dec(v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_681_; 
lean_inc(v_r_649_);
lean_inc(v_l_648_);
lean_inc(v_v_647_);
lean_inc(v_k_646_);
v_isSharedCheck_681_ = !lean_is_exclusive(v_r_632_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; lean_object* v_unused_683_; lean_object* v_unused_684_; lean_object* v_unused_685_; lean_object* v_unused_686_; 
v_unused_682_ = lean_ctor_get(v_r_632_, 4);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_r_632_, 3);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_r_632_, 2);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_r_632_, 1);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_r_632_, 0);
lean_dec(v_unused_686_);
v___x_654_ = v_r_632_;
v_isShared_655_ = v_isSharedCheck_681_;
goto v_resetjp_653_;
}
else
{
lean_dec(v_r_632_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_681_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___x_669_; lean_object* v___y_671_; 
v___x_656_ = lean_nat_add(v___x_626_, v_size_628_);
lean_dec(v_size_628_);
v___x_657_ = lean_nat_add(v___x_656_, v_size_627_);
lean_dec(v___x_656_);
v___x_669_ = lean_nat_add(v___x_626_, v_size_644_);
if (lean_obj_tag(v_l_648_) == 0)
{
lean_object* v_size_679_; 
v_size_679_ = lean_ctor_get(v_l_648_, 0);
lean_inc(v_size_679_);
v___y_671_ = v_size_679_;
goto v___jp_670_;
}
else
{
lean_object* v___x_680_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v___y_671_ = v___x_680_;
goto v___jp_670_;
}
v___jp_658_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_nat_add(v___y_659_, v___y_661_);
lean_dec(v___y_661_);
lean_dec(v___y_659_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v_r_620_);
lean_ctor_set(v___x_654_, 3, v_r_649_);
lean_ctor_set(v___x_654_, 2, v_v_618_);
lean_ctor_set(v___x_654_, 1, v_k_617_);
lean_ctor_set(v___x_654_, 0, v___x_662_);
v___x_664_ = v___x_654_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_r_649_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v_r_620_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 4, v___x_664_);
lean_ctor_set(v___x_642_, 3, v___y_660_);
lean_ctor_set(v___x_642_, 2, v_v_647_);
lean_ctor_set(v___x_642_, 1, v_k_646_);
lean_ctor_set(v___x_642_, 0, v___x_657_);
v___x_666_ = v___x_642_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_k_646_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_v_647_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v___y_660_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
v___jp_670_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_nat_add(v___x_669_, v___y_671_);
lean_dec(v___y_671_);
lean_dec(v___x_669_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v_l_648_);
lean_ctor_set(v___x_622_, 3, v_l_631_);
lean_ctor_set(v___x_622_, 2, v_v_630_);
lean_ctor_set(v___x_622_, 1, v_k_629_);
lean_ctor_set(v___x_622_, 0, v___x_672_);
v___x_674_ = v___x_622_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_k_629_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_v_630_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_l_648_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_nat_add(v___x_626_, v_size_627_);
if (lean_obj_tag(v_r_649_) == 0)
{
lean_object* v_size_676_; 
v_size_676_ = lean_ctor_get(v_r_649_, 0);
lean_inc(v_size_676_);
v___y_659_ = v___x_675_;
v___y_660_ = v___x_674_;
v___y_661_ = v_size_676_;
goto v___jp_658_;
}
else
{
lean_object* v___x_677_; 
v___x_677_ = lean_unsigned_to_nat(0u);
v___y_659_ = v___x_675_;
v___y_660_ = v___x_674_;
v___y_661_ = v___x_677_;
goto v___jp_658_;
}
}
}
}
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
lean_del_object(v___x_622_);
v___x_687_ = lean_nat_add(v___x_626_, v_size_628_);
lean_dec(v_size_628_);
v___x_688_ = lean_nat_add(v___x_687_, v_size_627_);
lean_dec(v___x_687_);
v___x_689_ = lean_nat_add(v___x_626_, v_size_627_);
v___x_690_ = lean_nat_add(v___x_689_, v_size_645_);
lean_dec(v___x_689_);
lean_inc_ref(v_r_620_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 4, v_r_620_);
lean_ctor_set(v___x_642_, 3, v_r_632_);
lean_ctor_set(v___x_642_, 2, v_v_618_);
lean_ctor_set(v___x_642_, 1, v_k_617_);
lean_ctor_set(v___x_642_, 0, v___x_690_);
v___x_692_ = v___x_642_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_r_632_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v_r_620_);
v___x_692_ = v_reuseFailAlloc_705_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_isSharedCheck_699_ = !lean_is_exclusive(v_r_620_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; lean_object* v_unused_701_; lean_object* v_unused_702_; lean_object* v_unused_703_; lean_object* v_unused_704_; 
v_unused_700_ = lean_ctor_get(v_r_620_, 4);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_r_620_, 3);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v_r_620_, 2);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v_r_620_, 1);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v_r_620_, 0);
lean_dec(v_unused_704_);
v___x_694_ = v_r_620_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_dec(v_r_620_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 4, v___x_692_);
lean_ctor_set(v___x_694_, 3, v_l_631_);
lean_ctor_set(v___x_694_, 2, v_v_630_);
lean_ctor_set(v___x_694_, 1, v_k_629_);
lean_ctor_set(v___x_694_, 0, v___x_688_);
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_k_629_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_v_630_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v___x_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_712_; 
v_l_712_ = lean_ctor_get(v_impl_625_, 3);
if (lean_obj_tag(v_l_712_) == 0)
{
lean_object* v_r_713_; lean_object* v_k_714_; lean_object* v_v_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_726_; 
lean_inc_ref(v_l_712_);
v_r_713_ = lean_ctor_get(v_impl_625_, 4);
v_k_714_ = lean_ctor_get(v_impl_625_, 1);
v_v_715_ = lean_ctor_get(v_impl_625_, 2);
v_isSharedCheck_726_ = !lean_is_exclusive(v_impl_625_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; lean_object* v_unused_728_; 
v_unused_727_ = lean_ctor_get(v_impl_625_, 3);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_impl_625_, 0);
lean_dec(v_unused_728_);
v___x_717_ = v_impl_625_;
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_r_713_);
lean_inc(v_v_715_);
lean_inc(v_k_714_);
lean_dec(v_impl_625_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_713_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 3, v_r_713_);
lean_ctor_set(v___x_717_, 2, v_v_618_);
lean_ctor_set(v___x_717_, 1, v_k_617_);
lean_ctor_set(v___x_717_, 0, v___x_626_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_r_713_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_r_713_);
v___x_721_ = v_reuseFailAlloc_725_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v___x_721_);
lean_ctor_set(v___x_622_, 3, v_l_712_);
lean_ctor_set(v___x_622_, 2, v_v_715_);
lean_ctor_set(v___x_622_, 1, v_k_714_);
lean_ctor_set(v___x_622_, 0, v___x_719_);
v___x_723_ = v___x_622_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_l_712_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_r_729_; 
v_r_729_ = lean_ctor_get(v_impl_625_, 4);
lean_inc(v_r_729_);
if (lean_obj_tag(v_r_729_) == 0)
{
lean_object* v_k_730_; lean_object* v_v_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_754_; 
lean_inc(v_l_712_);
v_k_730_ = lean_ctor_get(v_impl_625_, 1);
v_v_731_ = lean_ctor_get(v_impl_625_, 2);
v_isSharedCheck_754_ = !lean_is_exclusive(v_impl_625_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; lean_object* v_unused_756_; lean_object* v_unused_757_; 
v_unused_755_ = lean_ctor_get(v_impl_625_, 4);
lean_dec(v_unused_755_);
v_unused_756_ = lean_ctor_get(v_impl_625_, 3);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_impl_625_, 0);
lean_dec(v_unused_757_);
v___x_733_ = v_impl_625_;
v_isShared_734_ = v_isSharedCheck_754_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_v_731_);
lean_inc(v_k_730_);
lean_dec(v_impl_625_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_754_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_k_735_; lean_object* v_v_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_750_; 
v_k_735_ = lean_ctor_get(v_r_729_, 1);
v_v_736_ = lean_ctor_get(v_r_729_, 2);
v_isSharedCheck_750_ = !lean_is_exclusive(v_r_729_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; 
v_unused_751_ = lean_ctor_get(v_r_729_, 4);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_r_729_, 3);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_r_729_, 0);
lean_dec(v_unused_753_);
v___x_738_ = v_r_729_;
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_v_736_);
lean_inc(v_k_735_);
lean_dec(v_r_729_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = lean_unsigned_to_nat(3u);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v_l_712_);
lean_ctor_set(v___x_738_, 3, v_l_712_);
lean_ctor_set(v___x_738_, 2, v_v_731_);
lean_ctor_set(v___x_738_, 1, v_k_730_);
lean_ctor_set(v___x_738_, 0, v___x_626_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_k_730_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_v_731_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_l_712_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_l_712_);
v___x_742_ = v_reuseFailAlloc_749_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 4, v_l_712_);
lean_ctor_set(v___x_733_, 2, v_v_618_);
lean_ctor_set(v___x_733_, 1, v_k_617_);
lean_ctor_set(v___x_733_, 0, v___x_626_);
v___x_744_ = v___x_733_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_l_712_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_l_712_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v___x_744_);
lean_ctor_set(v___x_622_, 3, v___x_742_);
lean_ctor_set(v___x_622_, 2, v_v_736_);
lean_ctor_set(v___x_622_, 1, v_k_735_);
lean_ctor_set(v___x_622_, 0, v___x_740_);
v___x_746_ = v___x_622_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_735_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_736_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v___x_742_);
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
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = lean_unsigned_to_nat(2u);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v_r_729_);
lean_ctor_set(v___x_622_, 3, v_impl_625_);
lean_ctor_set(v___x_622_, 0, v___x_758_);
v___x_760_ = v___x_622_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_impl_625_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_r_729_);
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
case 1:
{
lean_object* v___x_763_; 
lean_dec(v_v_618_);
lean_dec(v_k_617_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 2, v_v_614_);
lean_ctor_set(v___x_622_, 1, v_k_613_);
v___x_763_ = v___x_622_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_size_616_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_l_619_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_r_620_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
default: 
{
lean_object* v_impl_765_; lean_object* v___x_766_; 
lean_dec(v_size_616_);
v_impl_765_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_613_, v_v_614_, v_r_620_);
v___x_766_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_619_) == 0)
{
lean_object* v_size_767_; lean_object* v_size_768_; lean_object* v_k_769_; lean_object* v_v_770_; lean_object* v_l_771_; lean_object* v_r_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_size_767_ = lean_ctor_get(v_l_619_, 0);
v_size_768_ = lean_ctor_get(v_impl_765_, 0);
v_k_769_ = lean_ctor_get(v_impl_765_, 1);
v_v_770_ = lean_ctor_get(v_impl_765_, 2);
v_l_771_ = lean_ctor_get(v_impl_765_, 3);
lean_inc(v_l_771_);
v_r_772_ = lean_ctor_get(v_impl_765_, 4);
v___x_773_ = lean_unsigned_to_nat(3u);
v___x_774_ = lean_nat_mul(v___x_773_, v_size_767_);
v___x_775_ = lean_nat_dec_lt(v___x_774_, v_size_768_);
lean_dec(v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
lean_dec(v_l_771_);
v___x_776_ = lean_nat_add(v___x_766_, v_size_767_);
v___x_777_ = lean_nat_add(v___x_776_, v_size_768_);
lean_dec(v___x_776_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v_impl_765_);
lean_ctor_set(v___x_622_, 0, v___x_777_);
v___x_779_ = v___x_622_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_l_619_);
lean_ctor_set(v_reuseFailAlloc_780_, 4, v_impl_765_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_844_; 
lean_inc(v_r_772_);
lean_inc(v_v_770_);
lean_inc(v_k_769_);
lean_inc(v_size_768_);
v_isSharedCheck_844_ = !lean_is_exclusive(v_impl_765_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; lean_object* v_unused_846_; lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; 
v_unused_845_ = lean_ctor_get(v_impl_765_, 4);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_impl_765_, 3);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_impl_765_, 2);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_impl_765_, 1);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_impl_765_, 0);
lean_dec(v_unused_849_);
v___x_782_ = v_impl_765_;
v_isShared_783_ = v_isSharedCheck_844_;
goto v_resetjp_781_;
}
else
{
lean_dec(v_impl_765_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_844_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_size_784_; lean_object* v_k_785_; lean_object* v_v_786_; lean_object* v_l_787_; lean_object* v_r_788_; lean_object* v_size_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_size_784_ = lean_ctor_get(v_l_771_, 0);
v_k_785_ = lean_ctor_get(v_l_771_, 1);
v_v_786_ = lean_ctor_get(v_l_771_, 2);
v_l_787_ = lean_ctor_get(v_l_771_, 3);
v_r_788_ = lean_ctor_get(v_l_771_, 4);
v_size_789_ = lean_ctor_get(v_r_772_, 0);
v___x_790_ = lean_unsigned_to_nat(2u);
v___x_791_ = lean_nat_mul(v___x_790_, v_size_789_);
v___x_792_ = lean_nat_dec_lt(v_size_784_, v___x_791_);
lean_dec(v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_820_; 
lean_inc(v_r_788_);
lean_inc(v_l_787_);
lean_inc(v_v_786_);
lean_inc(v_k_785_);
v_isSharedCheck_820_ = !lean_is_exclusive(v_l_771_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; lean_object* v_unused_822_; lean_object* v_unused_823_; lean_object* v_unused_824_; lean_object* v_unused_825_; 
v_unused_821_ = lean_ctor_get(v_l_771_, 4);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_l_771_, 3);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_l_771_, 2);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_l_771_, 1);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_l_771_, 0);
lean_dec(v_unused_825_);
v___x_794_ = v_l_771_;
v_isShared_795_ = v_isSharedCheck_820_;
goto v_resetjp_793_;
}
else
{
lean_dec(v_l_771_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_820_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_810_; 
v___x_796_ = lean_nat_add(v___x_766_, v_size_767_);
v___x_797_ = lean_nat_add(v___x_796_, v_size_768_);
lean_dec(v_size_768_);
if (lean_obj_tag(v_l_787_) == 0)
{
lean_object* v_size_818_; 
v_size_818_ = lean_ctor_get(v_l_787_, 0);
lean_inc(v_size_818_);
v___y_810_ = v_size_818_;
goto v___jp_809_;
}
else
{
lean_object* v___x_819_; 
v___x_819_ = lean_unsigned_to_nat(0u);
v___y_810_ = v___x_819_;
goto v___jp_809_;
}
v___jp_798_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_nat_add(v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec(v___y_800_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 4, v_r_772_);
lean_ctor_set(v___x_794_, 3, v_r_788_);
lean_ctor_set(v___x_794_, 2, v_v_770_);
lean_ctor_set(v___x_794_, 1, v_k_769_);
lean_ctor_set(v___x_794_, 0, v___x_802_);
v___x_804_ = v___x_794_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_r_788_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_r_772_);
v___x_804_ = v_reuseFailAlloc_808_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_806_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v___x_804_);
lean_ctor_set(v___x_782_, 3, v___y_799_);
lean_ctor_set(v___x_782_, 2, v_v_786_);
lean_ctor_set(v___x_782_, 1, v_k_785_);
lean_ctor_set(v___x_782_, 0, v___x_797_);
v___x_806_ = v___x_782_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_785_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_786_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v___y_799_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
v___jp_809_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = lean_nat_add(v___x_796_, v___y_810_);
lean_dec(v___y_810_);
lean_dec(v___x_796_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v_l_787_);
lean_ctor_set(v___x_622_, 0, v___x_811_);
v___x_813_ = v___x_622_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_l_619_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v_l_787_);
v___x_813_ = v_reuseFailAlloc_817_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; 
v___x_814_ = lean_nat_add(v___x_766_, v_size_789_);
if (lean_obj_tag(v_r_788_) == 0)
{
lean_object* v_size_815_; 
v_size_815_ = lean_ctor_get(v_r_788_, 0);
lean_inc(v_size_815_);
v___y_799_ = v___x_813_;
v___y_800_ = v___x_814_;
v___y_801_ = v_size_815_;
goto v___jp_798_;
}
else
{
lean_object* v___x_816_; 
v___x_816_ = lean_unsigned_to_nat(0u);
v___y_799_ = v___x_813_;
v___y_800_ = v___x_814_;
v___y_801_ = v___x_816_;
goto v___jp_798_;
}
}
}
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
lean_del_object(v___x_622_);
v___x_826_ = lean_nat_add(v___x_766_, v_size_767_);
v___x_827_ = lean_nat_add(v___x_826_, v_size_768_);
lean_dec(v_size_768_);
v___x_828_ = lean_nat_add(v___x_826_, v_size_784_);
lean_dec(v___x_826_);
lean_inc_ref(v_l_619_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v_l_771_);
lean_ctor_set(v___x_782_, 3, v_l_619_);
lean_ctor_set(v___x_782_, 2, v_v_618_);
lean_ctor_set(v___x_782_, 1, v_k_617_);
lean_ctor_set(v___x_782_, 0, v___x_828_);
v___x_830_ = v___x_782_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v_l_619_);
lean_ctor_set(v_reuseFailAlloc_843_, 4, v_l_771_);
v___x_830_ = v_reuseFailAlloc_843_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_isSharedCheck_837_ = !lean_is_exclusive(v_l_619_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_838_ = lean_ctor_get(v_l_619_, 4);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_l_619_, 3);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_l_619_, 2);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_l_619_, 1);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_l_619_, 0);
lean_dec(v_unused_842_);
v___x_832_ = v_l_619_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_dec(v_l_619_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 4, v_r_772_);
lean_ctor_set(v___x_832_, 3, v___x_830_);
lean_ctor_set(v___x_832_, 2, v_v_770_);
lean_ctor_set(v___x_832_, 1, v_k_769_);
lean_ctor_set(v___x_832_, 0, v___x_827_);
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v_r_772_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_850_; 
v_l_850_ = lean_ctor_get(v_impl_765_, 3);
lean_inc(v_l_850_);
if (lean_obj_tag(v_l_850_) == 0)
{
lean_object* v_r_851_; lean_object* v_k_852_; lean_object* v_v_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_876_; 
v_r_851_ = lean_ctor_get(v_impl_765_, 4);
v_k_852_ = lean_ctor_get(v_impl_765_, 1);
v_v_853_ = lean_ctor_get(v_impl_765_, 2);
v_isSharedCheck_876_ = !lean_is_exclusive(v_impl_765_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; lean_object* v_unused_878_; 
v_unused_877_ = lean_ctor_get(v_impl_765_, 3);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v_impl_765_, 0);
lean_dec(v_unused_878_);
v___x_855_ = v_impl_765_;
v_isShared_856_ = v_isSharedCheck_876_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_r_851_);
lean_inc(v_v_853_);
lean_inc(v_k_852_);
lean_dec(v_impl_765_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_876_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_k_857_; lean_object* v_v_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_872_; 
v_k_857_ = lean_ctor_get(v_l_850_, 1);
v_v_858_ = lean_ctor_get(v_l_850_, 2);
v_isSharedCheck_872_ = !lean_is_exclusive(v_l_850_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; 
v_unused_873_ = lean_ctor_get(v_l_850_, 4);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_l_850_, 3);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_l_850_, 0);
lean_dec(v_unused_875_);
v___x_860_ = v_l_850_;
v_isShared_861_ = v_isSharedCheck_872_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_v_858_);
lean_inc(v_k_857_);
lean_dec(v_l_850_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_872_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_851_, 2);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 4, v_r_851_);
lean_ctor_set(v___x_860_, 3, v_r_851_);
lean_ctor_set(v___x_860_, 2, v_v_618_);
lean_ctor_set(v___x_860_, 1, v_k_617_);
lean_ctor_set(v___x_860_, 0, v___x_766_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_871_, 3, v_r_851_);
lean_ctor_set(v_reuseFailAlloc_871_, 4, v_r_851_);
v___x_864_ = v_reuseFailAlloc_871_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
lean_inc(v_r_851_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 3, v_r_851_);
lean_ctor_set(v___x_855_, 0, v___x_766_);
v___x_866_ = v___x_855_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_k_852_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_v_853_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_r_851_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_r_851_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v___x_866_);
lean_ctor_set(v___x_622_, 3, v___x_864_);
lean_ctor_set(v___x_622_, 2, v_v_858_);
lean_ctor_set(v___x_622_, 1, v_k_857_);
lean_ctor_set(v___x_622_, 0, v___x_862_);
v___x_868_ = v___x_622_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_k_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_v_858_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
else
{
lean_object* v_r_879_; 
v_r_879_ = lean_ctor_get(v_impl_765_, 4);
lean_inc(v_r_879_);
if (lean_obj_tag(v_r_879_) == 0)
{
lean_object* v_k_880_; lean_object* v_v_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_892_; 
v_k_880_ = lean_ctor_get(v_impl_765_, 1);
v_v_881_ = lean_ctor_get(v_impl_765_, 2);
v_isSharedCheck_892_ = !lean_is_exclusive(v_impl_765_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; lean_object* v_unused_894_; lean_object* v_unused_895_; 
v_unused_893_ = lean_ctor_get(v_impl_765_, 4);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_impl_765_, 3);
lean_dec(v_unused_894_);
v_unused_895_ = lean_ctor_get(v_impl_765_, 0);
lean_dec(v_unused_895_);
v___x_883_ = v_impl_765_;
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_v_881_);
lean_inc(v_k_880_);
lean_dec(v_impl_765_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(3u);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 4, v_l_850_);
lean_ctor_set(v___x_883_, 2, v_v_618_);
lean_ctor_set(v___x_883_, 1, v_k_617_);
lean_ctor_set(v___x_883_, 0, v___x_766_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v_l_850_);
lean_ctor_set(v_reuseFailAlloc_891_, 4, v_l_850_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v_r_879_);
lean_ctor_set(v___x_622_, 3, v___x_887_);
lean_ctor_set(v___x_622_, 2, v_v_881_);
lean_ctor_set(v___x_622_, 1, v_k_880_);
lean_ctor_set(v___x_622_, 0, v___x_885_);
v___x_889_ = v___x_622_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_k_880_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_v_881_);
lean_ctor_set(v_reuseFailAlloc_890_, 3, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_890_, 4, v_r_879_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_unsigned_to_nat(2u);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v_impl_765_);
lean_ctor_set(v___x_622_, 3, v_r_879_);
lean_ctor_set(v___x_622_, 0, v___x_896_);
v___x_898_ = v___x_622_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_r_879_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v_impl_765_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
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
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v_k_613_);
lean_ctor_set(v___x_902_, 2, v_v_614_);
lean_ctor_set(v___x_902_, 3, v_t_615_);
lean_ctor_set(v___x_902_, 4, v_t_615_);
return v___x_902_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object* v_k_903_, lean_object* v_t_904_){
_start:
{
if (lean_obj_tag(v_t_904_) == 0)
{
lean_object* v_k_905_; lean_object* v_l_906_; lean_object* v_r_907_; uint8_t v___x_908_; 
v_k_905_ = lean_ctor_get(v_t_904_, 1);
v_l_906_ = lean_ctor_get(v_t_904_, 3);
v_r_907_ = lean_ctor_get(v_t_904_, 4);
v___x_908_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_903_, v_k_905_);
switch(v___x_908_)
{
case 0:
{
v_t_904_ = v_l_906_;
goto _start;
}
case 1:
{
uint8_t v___x_910_; 
v___x_910_ = 1;
return v___x_910_;
}
default: 
{
v_t_904_ = v_r_907_;
goto _start;
}
}
}
else
{
uint8_t v___x_912_; 
v___x_912_ = 0;
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object* v_k_913_, lean_object* v_t_914_){
_start:
{
uint8_t v_res_915_; lean_object* v_r_916_; 
v_res_915_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_913_, v_t_914_);
lean_dec(v_t_914_);
lean_dec(v_k_913_);
v_r_916_ = lean_box(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object* v___y_917_){
_start:
{
lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_918_ = lean_box(1);
v___x_919_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v___y_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_box(0);
v___x_921_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___y_917_, v___x_920_, v___x_918_);
return v___x_921_;
}
else
{
lean_dec(v___y_917_);
return v___x_918_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object* v_00_u03b2_924_, lean_object* v_k_925_, lean_object* v_t_926_){
_start:
{
uint8_t v___x_927_; 
v___x_927_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_925_, v_t_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object* v_00_u03b2_928_, lean_object* v_k_929_, lean_object* v_t_930_){
_start:
{
uint8_t v_res_931_; lean_object* v_r_932_; 
v_res_931_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(v_00_u03b2_928_, v_k_929_, v_t_930_);
lean_dec(v_t_930_);
lean_dec(v_k_929_);
v_r_932_ = lean_box(v_res_931_);
return v_r_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object* v_00_u03b2_933_, lean_object* v_k_934_, lean_object* v_v_935_, lean_object* v_t_936_, lean_object* v_hl_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_934_, v_v_935_, v_t_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_939_, lean_object* v_a_940_, lean_object* v_b_941_, lean_object* v_c_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = lean_apply_2(v_f_939_, v_a_940_, v_c_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_944_, lean_object* v_____do__lift_945_){
_start:
{
lean_object* v_a_946_; lean_object* v___x_947_; 
v_a_946_ = lean_ctor_get(v_____do__lift_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v_____do__lift_945_);
v___x_947_ = lean_apply_2(v_toPure_944_, lean_box(0), v_a_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object* v_inst_948_, lean_object* v_m_949_, lean_object* v_init_950_, lean_object* v_f_951_){
_start:
{
lean_object* v_toApplicative_952_; lean_object* v_toBind_953_; lean_object* v_toPure_954_; lean_object* v___f_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___x_958_; 
v_toApplicative_952_ = lean_ctor_get(v_inst_948_, 0);
v_toBind_953_ = lean_ctor_get(v_inst_948_, 1);
lean_inc(v_toBind_953_);
v_toPure_954_ = lean_ctor_get(v_toApplicative_952_, 1);
lean_inc(v_toPure_954_);
v___f_955_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_955_, 0, v_f_951_);
v___x_956_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_948_, v___f_955_, v_init_950_, v_m_949_);
v___f_957_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_957_, 0, v_toPure_954_);
v___x_958_ = lean_apply_4(v_toBind_953_, lean_box(0), lean_box(0), v___x_956_, v___f_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object* v_m_959_, lean_object* v_inst_960_, lean_object* v_00_u03b2_961_, lean_object* v_m_962_, lean_object* v_init_963_, lean_object* v_f_964_){
_start:
{
lean_object* v_toApplicative_965_; lean_object* v_toBind_966_; lean_object* v_toPure_967_; lean_object* v___f_968_; lean_object* v___x_969_; lean_object* v___f_970_; lean_object* v___x_971_; 
v_toApplicative_965_ = lean_ctor_get(v_inst_960_, 0);
v_toBind_966_ = lean_ctor_get(v_inst_960_, 1);
lean_inc(v_toBind_966_);
v_toPure_967_ = lean_ctor_get(v_toApplicative_965_, 1);
lean_inc(v_toPure_967_);
v___f_968_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_968_, 0, v_f_964_);
v___x_969_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_960_, v___f_968_, v_init_963_, v_m_962_);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_970_, 0, v_toPure_967_);
v___x_971_ = lean_apply_4(v_toBind_966_, lean_box(0), lean_box(0), v___x_969_, v___f_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_973_, 0, lean_box(0));
lean_closure_set(v___x_973_, 1, v_inst_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_974_, lean_object* v_inst_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_976_, 0, lean_box(0));
lean_closure_set(v___x_976_, 1, v_inst_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_977_, lean_object* v_fvarId_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_fvarId_978_, v_s_977_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_box(0);
v___x_981_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_978_, v___x_980_, v_s_977_);
return v___x_981_;
}
else
{
lean_dec(v_fvarId_978_);
return v_s_977_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_982_, lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_983_) == 0)
{
lean_object* v_k_984_; lean_object* v_l_985_; lean_object* v_r_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_k_984_ = lean_ctor_get(v_x_983_, 1);
lean_inc(v_k_984_);
v_l_985_ = lean_ctor_get(v_x_983_, 3);
lean_inc(v_l_985_);
v_r_986_ = lean_ctor_get(v_x_983_, 4);
lean_inc(v_r_986_);
lean_dec_ref_known(v_x_983_, 5);
v___x_987_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_982_, v_l_985_);
v___x_988_ = l_Lean_FVarIdSet_insert(v___x_987_, v_k_984_);
v_init_982_ = v___x_988_;
v_x_983_ = v_r_986_;
goto _start;
}
else
{
return v_init_982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_990_, lean_object* v_vs_u2082_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_991_, v_vs_u2081_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_993_, lean_object* v_t_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_993_, v_t_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_996_){
_start:
{
lean_object* v___f_997_; lean_object* v___x_998_; 
v___f_997_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_998_ = l_Std_TreeSet_ofList___redArg(v_l_996_, v___f_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object* v_l_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_FVarIdSet_ofList(v_l_999_);
lean_dec(v_l_999_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_1001_){
_start:
{
lean_object* v___f_1002_; lean_object* v___x_1003_; 
v___f_1002_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1003_ = l_Std_TreeSet_ofArray___redArg(v_l_1001_, v___f_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_FVarIdSet_ofArray(v_l_1004_);
lean_dec_ref(v_l_1004_);
return v_res_1005_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_unsigned_to_nat(16u);
v___x_1008_ = lean_mk_array(v___x_1007_, v___x_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1016_, lean_object* v_fvarId_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1017_, v_a_1018_, v_s_1016_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1020_, lean_object* v_s_1021_, lean_object* v_fvarId_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1022_, v_a_1023_, v_s_1021_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_box(1);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg();
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_box(1);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_box(1);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg___boxed(lean_object* v___dummy_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_instEmptyCollectionFVarIdMap___redArg();
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_box(1);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_box(1);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg___boxed(lean_object* v___dummy_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_instInhabitedFVarIdMap___redArg();
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_box(1);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_box(0);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_box(0);
return v___x_1044_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_name_eq(v_x_1045_, v_x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_res_1050_ = l_Lean_instBEqMVarId_beq(v_x_1048_, v_x_1049_);
lean_dec(v_x_1049_);
lean_dec(v_x_1048_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1054_){
_start:
{
uint64_t v___x_1055_; 
v___x_1055_ = 0ULL;
if (lean_obj_tag(v_x_1054_) == 0)
{
uint64_t v___x_1056_; 
v___x_1056_ = 8934034000889494153ULL;
return v___x_1056_;
}
else
{
uint64_t v_hash_1057_; uint64_t v___x_1058_; 
v_hash_1057_ = lean_ctor_get_uint64(v_x_1054_, sizeof(void*)*2);
v___x_1058_ = lean_uint64_mix_hash(v___x_1055_, v_hash_1057_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1059_){
_start:
{
uint64_t v_res_1060_; lean_object* v_r_1061_; 
v_res_1060_ = l_Lean_instHashableMVarId_hash(v_x_1059_);
lean_dec(v_x_1059_);
v_r_1061_ = lean_box_uint64(v_res_1060_);
return v_r_1061_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_box(1);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_box(1);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_box(1);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_box(1);
return v___x_1068_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1069_, lean_object* v_t_1070_){
_start:
{
if (lean_obj_tag(v_t_1070_) == 0)
{
lean_object* v_k_1071_; lean_object* v_l_1072_; lean_object* v_r_1073_; uint8_t v___x_1074_; 
v_k_1071_ = lean_ctor_get(v_t_1070_, 1);
v_l_1072_ = lean_ctor_get(v_t_1070_, 3);
v_r_1073_ = lean_ctor_get(v_t_1070_, 4);
v___x_1074_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1069_, v_k_1071_);
switch(v___x_1074_)
{
case 0:
{
v_t_1070_ = v_l_1072_;
goto _start;
}
case 1:
{
uint8_t v___x_1076_; 
v___x_1076_ = 1;
return v___x_1076_;
}
default: 
{
v_t_1070_ = v_r_1073_;
goto _start;
}
}
}
else
{
uint8_t v___x_1078_; 
v___x_1078_ = 0;
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1079_, lean_object* v_t_1080_){
_start:
{
uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_res_1081_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1079_, v_t_1080_);
lean_dec(v_t_1080_);
lean_dec(v_k_1079_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1083_, lean_object* v_v_1084_, lean_object* v_t_1085_){
_start:
{
if (lean_obj_tag(v_t_1085_) == 0)
{
lean_object* v_size_1086_; lean_object* v_k_1087_; lean_object* v_v_1088_; lean_object* v_l_1089_; lean_object* v_r_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1370_; 
v_size_1086_ = lean_ctor_get(v_t_1085_, 0);
v_k_1087_ = lean_ctor_get(v_t_1085_, 1);
v_v_1088_ = lean_ctor_get(v_t_1085_, 2);
v_l_1089_ = lean_ctor_get(v_t_1085_, 3);
v_r_1090_ = lean_ctor_get(v_t_1085_, 4);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_t_1085_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1092_ = v_t_1085_;
v_isShared_1093_ = v_isSharedCheck_1370_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_r_1090_);
lean_inc(v_l_1089_);
lean_inc(v_v_1088_);
lean_inc(v_k_1087_);
lean_inc(v_size_1086_);
lean_dec(v_t_1085_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1370_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
uint8_t v___x_1094_; 
v___x_1094_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1083_, v_k_1087_);
switch(v___x_1094_)
{
case 0:
{
lean_object* v_impl_1095_; lean_object* v___x_1096_; 
lean_dec(v_size_1086_);
v_impl_1095_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1083_, v_v_1084_, v_l_1089_);
v___x_1096_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1090_) == 0)
{
lean_object* v_size_1097_; lean_object* v_size_1098_; lean_object* v_k_1099_; lean_object* v_v_1100_; lean_object* v_l_1101_; lean_object* v_r_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_size_1097_ = lean_ctor_get(v_r_1090_, 0);
v_size_1098_ = lean_ctor_get(v_impl_1095_, 0);
v_k_1099_ = lean_ctor_get(v_impl_1095_, 1);
v_v_1100_ = lean_ctor_get(v_impl_1095_, 2);
v_l_1101_ = lean_ctor_get(v_impl_1095_, 3);
v_r_1102_ = lean_ctor_get(v_impl_1095_, 4);
lean_inc(v_r_1102_);
v___x_1103_ = lean_unsigned_to_nat(3u);
v___x_1104_ = lean_nat_mul(v___x_1103_, v_size_1097_);
v___x_1105_ = lean_nat_dec_lt(v___x_1104_, v_size_1098_);
lean_dec(v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
lean_dec(v_r_1102_);
v___x_1106_ = lean_nat_add(v___x_1096_, v_size_1098_);
v___x_1107_ = lean_nat_add(v___x_1106_, v_size_1097_);
lean_dec(v___x_1106_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 3, v_impl_1095_);
lean_ctor_set(v___x_1092_, 0, v___x_1107_);
v___x_1109_ = v___x_1092_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_impl_1095_);
lean_ctor_set(v_reuseFailAlloc_1110_, 4, v_r_1090_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
else
{
lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1176_; 
lean_inc(v_l_1101_);
lean_inc(v_v_1100_);
lean_inc(v_k_1099_);
lean_inc(v_size_1098_);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_impl_1095_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; lean_object* v_unused_1178_; lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; 
v_unused_1177_ = lean_ctor_get(v_impl_1095_, 4);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_impl_1095_, 3);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_impl_1095_, 2);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_impl_1095_, 1);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_impl_1095_, 0);
lean_dec(v_unused_1181_);
v___x_1112_ = v_impl_1095_;
v_isShared_1113_ = v_isSharedCheck_1176_;
goto v_resetjp_1111_;
}
else
{
lean_dec(v_impl_1095_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1176_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_size_1114_; lean_object* v_size_1115_; lean_object* v_k_1116_; lean_object* v_v_1117_; lean_object* v_l_1118_; lean_object* v_r_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v_size_1114_ = lean_ctor_get(v_l_1101_, 0);
v_size_1115_ = lean_ctor_get(v_r_1102_, 0);
v_k_1116_ = lean_ctor_get(v_r_1102_, 1);
v_v_1117_ = lean_ctor_get(v_r_1102_, 2);
v_l_1118_ = lean_ctor_get(v_r_1102_, 3);
v_r_1119_ = lean_ctor_get(v_r_1102_, 4);
v___x_1120_ = lean_unsigned_to_nat(2u);
v___x_1121_ = lean_nat_mul(v___x_1120_, v_size_1114_);
v___x_1122_ = lean_nat_dec_lt(v_size_1115_, v___x_1121_);
lean_dec(v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1151_; 
lean_inc(v_r_1119_);
lean_inc(v_l_1118_);
lean_inc(v_v_1117_);
lean_inc(v_k_1116_);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_r_1102_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; lean_object* v_unused_1153_; lean_object* v_unused_1154_; lean_object* v_unused_1155_; lean_object* v_unused_1156_; 
v_unused_1152_ = lean_ctor_get(v_r_1102_, 4);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_r_1102_, 3);
lean_dec(v_unused_1153_);
v_unused_1154_ = lean_ctor_get(v_r_1102_, 2);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_r_1102_, 1);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_r_1102_, 0);
lean_dec(v_unused_1156_);
v___x_1124_ = v_r_1102_;
v_isShared_1125_ = v_isSharedCheck_1151_;
goto v_resetjp_1123_;
}
else
{
lean_dec(v_r_1102_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1151_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___x_1139_; lean_object* v___y_1141_; 
v___x_1126_ = lean_nat_add(v___x_1096_, v_size_1098_);
lean_dec(v_size_1098_);
v___x_1127_ = lean_nat_add(v___x_1126_, v_size_1097_);
lean_dec(v___x_1126_);
v___x_1139_ = lean_nat_add(v___x_1096_, v_size_1114_);
if (lean_obj_tag(v_l_1118_) == 0)
{
lean_object* v_size_1149_; 
v_size_1149_ = lean_ctor_get(v_l_1118_, 0);
lean_inc(v_size_1149_);
v___y_1141_ = v_size_1149_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_unsigned_to_nat(0u);
v___y_1141_ = v___x_1150_;
goto v___jp_1140_;
}
v___jp_1128_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_nat_add(v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec(v___y_1130_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 4, v_r_1090_);
lean_ctor_set(v___x_1124_, 3, v_r_1119_);
lean_ctor_set(v___x_1124_, 2, v_v_1088_);
lean_ctor_set(v___x_1124_, 1, v_k_1087_);
lean_ctor_set(v___x_1124_, 0, v___x_1132_);
v___x_1134_ = v___x_1124_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v_r_1119_);
lean_ctor_set(v_reuseFailAlloc_1138_, 4, v_r_1090_);
v___x_1134_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 4, v___x_1134_);
lean_ctor_set(v___x_1112_, 3, v___y_1129_);
lean_ctor_set(v___x_1112_, 2, v_v_1117_);
lean_ctor_set(v___x_1112_, 1, v_k_1116_);
lean_ctor_set(v___x_1112_, 0, v___x_1127_);
v___x_1136_ = v___x_1112_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_k_1116_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_v_1117_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v___y_1129_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
v___jp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = lean_nat_add(v___x_1139_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec(v___x_1139_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v_l_1118_);
lean_ctor_set(v___x_1092_, 3, v_l_1101_);
lean_ctor_set(v___x_1092_, 2, v_v_1100_);
lean_ctor_set(v___x_1092_, 1, v_k_1099_);
lean_ctor_set(v___x_1092_, 0, v___x_1142_);
v___x_1144_ = v___x_1092_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_k_1099_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_v_1100_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_l_1101_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_l_1118_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_nat_add(v___x_1096_, v_size_1097_);
if (lean_obj_tag(v_r_1119_) == 0)
{
lean_object* v_size_1146_; 
v_size_1146_ = lean_ctor_get(v_r_1119_, 0);
lean_inc(v_size_1146_);
v___y_1129_ = v___x_1144_;
v___y_1130_ = v___x_1145_;
v___y_1131_ = v_size_1146_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_unsigned_to_nat(0u);
v___y_1129_ = v___x_1144_;
v___y_1130_ = v___x_1145_;
v___y_1131_ = v___x_1147_;
goto v___jp_1128_;
}
}
}
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_del_object(v___x_1092_);
v___x_1157_ = lean_nat_add(v___x_1096_, v_size_1098_);
lean_dec(v_size_1098_);
v___x_1158_ = lean_nat_add(v___x_1157_, v_size_1097_);
lean_dec(v___x_1157_);
v___x_1159_ = lean_nat_add(v___x_1096_, v_size_1097_);
v___x_1160_ = lean_nat_add(v___x_1159_, v_size_1115_);
lean_dec(v___x_1159_);
lean_inc_ref(v_r_1090_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 4, v_r_1090_);
lean_ctor_set(v___x_1112_, 3, v_r_1102_);
lean_ctor_set(v___x_1112_, 2, v_v_1088_);
lean_ctor_set(v___x_1112_, 1, v_k_1087_);
lean_ctor_set(v___x_1112_, 0, v___x_1160_);
v___x_1162_ = v___x_1112_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1175_, 3, v_r_1102_);
lean_ctor_set(v_reuseFailAlloc_1175_, 4, v_r_1090_);
v___x_1162_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v_isSharedCheck_1169_ = !lean_is_exclusive(v_r_1090_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; lean_object* v_unused_1173_; lean_object* v_unused_1174_; 
v_unused_1170_ = lean_ctor_get(v_r_1090_, 4);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_r_1090_, 3);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_r_1090_, 2);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_r_1090_, 1);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_r_1090_, 0);
lean_dec(v_unused_1174_);
v___x_1164_ = v_r_1090_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_dec(v_r_1090_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 4, v___x_1162_);
lean_ctor_set(v___x_1164_, 3, v_l_1101_);
lean_ctor_set(v___x_1164_, 2, v_v_1100_);
lean_ctor_set(v___x_1164_, 1, v_k_1099_);
lean_ctor_set(v___x_1164_, 0, v___x_1158_);
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_k_1099_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_v_1100_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_l_1101_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v___x_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1182_; 
v_l_1182_ = lean_ctor_get(v_impl_1095_, 3);
if (lean_obj_tag(v_l_1182_) == 0)
{
lean_object* v_r_1183_; lean_object* v_k_1184_; lean_object* v_v_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1196_; 
lean_inc_ref(v_l_1182_);
v_r_1183_ = lean_ctor_get(v_impl_1095_, 4);
v_k_1184_ = lean_ctor_get(v_impl_1095_, 1);
v_v_1185_ = lean_ctor_get(v_impl_1095_, 2);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_impl_1095_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; lean_object* v_unused_1198_; 
v_unused_1197_ = lean_ctor_get(v_impl_1095_, 3);
lean_dec(v_unused_1197_);
v_unused_1198_ = lean_ctor_get(v_impl_1095_, 0);
lean_dec(v_unused_1198_);
v___x_1187_ = v_impl_1095_;
v_isShared_1188_ = v_isSharedCheck_1196_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_r_1183_);
lean_inc(v_v_1185_);
lean_inc(v_k_1184_);
lean_dec(v_impl_1095_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1196_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1183_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 3, v_r_1183_);
lean_ctor_set(v___x_1187_, 2, v_v_1088_);
lean_ctor_set(v___x_1187_, 1, v_k_1087_);
lean_ctor_set(v___x_1187_, 0, v___x_1096_);
v___x_1191_ = v___x_1187_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v_r_1183_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v_r_1183_);
v___x_1191_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1193_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v___x_1191_);
lean_ctor_set(v___x_1092_, 3, v_l_1182_);
lean_ctor_set(v___x_1092_, 2, v_v_1185_);
lean_ctor_set(v___x_1092_, 1, v_k_1184_);
lean_ctor_set(v___x_1092_, 0, v___x_1189_);
v___x_1193_ = v___x_1092_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_k_1184_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_v_1185_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_l_1182_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_r_1199_; 
v_r_1199_ = lean_ctor_get(v_impl_1095_, 4);
lean_inc(v_r_1199_);
if (lean_obj_tag(v_r_1199_) == 0)
{
lean_object* v_k_1200_; lean_object* v_v_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1224_; 
lean_inc(v_l_1182_);
v_k_1200_ = lean_ctor_get(v_impl_1095_, 1);
v_v_1201_ = lean_ctor_get(v_impl_1095_, 2);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_impl_1095_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; lean_object* v_unused_1226_; lean_object* v_unused_1227_; 
v_unused_1225_ = lean_ctor_get(v_impl_1095_, 4);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_impl_1095_, 3);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_impl_1095_, 0);
lean_dec(v_unused_1227_);
v___x_1203_ = v_impl_1095_;
v_isShared_1204_ = v_isSharedCheck_1224_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_v_1201_);
lean_inc(v_k_1200_);
lean_dec(v_impl_1095_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1224_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_k_1205_; lean_object* v_v_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1220_; 
v_k_1205_ = lean_ctor_get(v_r_1199_, 1);
v_v_1206_ = lean_ctor_get(v_r_1199_, 2);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_r_1199_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; lean_object* v_unused_1222_; lean_object* v_unused_1223_; 
v_unused_1221_ = lean_ctor_get(v_r_1199_, 4);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_r_1199_, 3);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_r_1199_, 0);
lean_dec(v_unused_1223_);
v___x_1208_ = v_r_1199_;
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_v_1206_);
lean_inc(v_k_1205_);
lean_dec(v_r_1199_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_unsigned_to_nat(3u);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 4, v_l_1182_);
lean_ctor_set(v___x_1208_, 3, v_l_1182_);
lean_ctor_set(v___x_1208_, 2, v_v_1201_);
lean_ctor_set(v___x_1208_, 1, v_k_1200_);
lean_ctor_set(v___x_1208_, 0, v___x_1096_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_k_1200_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_v_1201_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_l_1182_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v_l_1182_);
v___x_1212_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1214_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 4, v_l_1182_);
lean_ctor_set(v___x_1203_, 2, v_v_1088_);
lean_ctor_set(v___x_1203_, 1, v_k_1087_);
lean_ctor_set(v___x_1203_, 0, v___x_1096_);
v___x_1214_ = v___x_1203_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v_l_1182_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v_l_1182_);
v___x_1214_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v___x_1214_);
lean_ctor_set(v___x_1092_, 3, v___x_1212_);
lean_ctor_set(v___x_1092_, 2, v_v_1206_);
lean_ctor_set(v___x_1092_, 1, v_k_1205_);
lean_ctor_set(v___x_1092_, 0, v___x_1210_);
v___x_1216_ = v___x_1092_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_k_1205_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_v_1206_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = lean_unsigned_to_nat(2u);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v_r_1199_);
lean_ctor_set(v___x_1092_, 3, v_impl_1095_);
lean_ctor_set(v___x_1092_, 0, v___x_1228_);
v___x_1230_ = v___x_1092_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_impl_1095_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_r_1199_);
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
case 1:
{
lean_object* v___x_1233_; 
lean_dec(v_v_1088_);
lean_dec(v_k_1087_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 2, v_v_1084_);
lean_ctor_set(v___x_1092_, 1, v_k_1083_);
v___x_1233_ = v___x_1092_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_size_1086_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v_l_1089_);
lean_ctor_set(v_reuseFailAlloc_1234_, 4, v_r_1090_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
default: 
{
lean_object* v_impl_1235_; lean_object* v___x_1236_; 
lean_dec(v_size_1086_);
v_impl_1235_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1083_, v_v_1084_, v_r_1090_);
v___x_1236_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1089_) == 0)
{
lean_object* v_size_1237_; lean_object* v_size_1238_; lean_object* v_k_1239_; lean_object* v_v_1240_; lean_object* v_l_1241_; lean_object* v_r_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_size_1237_ = lean_ctor_get(v_l_1089_, 0);
v_size_1238_ = lean_ctor_get(v_impl_1235_, 0);
v_k_1239_ = lean_ctor_get(v_impl_1235_, 1);
v_v_1240_ = lean_ctor_get(v_impl_1235_, 2);
v_l_1241_ = lean_ctor_get(v_impl_1235_, 3);
lean_inc(v_l_1241_);
v_r_1242_ = lean_ctor_get(v_impl_1235_, 4);
v___x_1243_ = lean_unsigned_to_nat(3u);
v___x_1244_ = lean_nat_mul(v___x_1243_, v_size_1237_);
v___x_1245_ = lean_nat_dec_lt(v___x_1244_, v_size_1238_);
lean_dec(v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_dec(v_l_1241_);
v___x_1246_ = lean_nat_add(v___x_1236_, v_size_1237_);
v___x_1247_ = lean_nat_add(v___x_1246_, v_size_1238_);
lean_dec(v___x_1246_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v_impl_1235_);
lean_ctor_set(v___x_1092_, 0, v___x_1247_);
v___x_1249_ = v___x_1092_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_l_1089_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_impl_1235_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
else
{
lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1314_; 
lean_inc(v_r_1242_);
lean_inc(v_v_1240_);
lean_inc(v_k_1239_);
lean_inc(v_size_1238_);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_impl_1235_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; lean_object* v_unused_1316_; lean_object* v_unused_1317_; lean_object* v_unused_1318_; lean_object* v_unused_1319_; 
v_unused_1315_ = lean_ctor_get(v_impl_1235_, 4);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v_impl_1235_, 3);
lean_dec(v_unused_1316_);
v_unused_1317_ = lean_ctor_get(v_impl_1235_, 2);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_impl_1235_, 1);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_impl_1235_, 0);
lean_dec(v_unused_1319_);
v___x_1252_ = v_impl_1235_;
v_isShared_1253_ = v_isSharedCheck_1314_;
goto v_resetjp_1251_;
}
else
{
lean_dec(v_impl_1235_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1314_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_size_1254_; lean_object* v_k_1255_; lean_object* v_v_1256_; lean_object* v_l_1257_; lean_object* v_r_1258_; lean_object* v_size_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_size_1254_ = lean_ctor_get(v_l_1241_, 0);
v_k_1255_ = lean_ctor_get(v_l_1241_, 1);
v_v_1256_ = lean_ctor_get(v_l_1241_, 2);
v_l_1257_ = lean_ctor_get(v_l_1241_, 3);
v_r_1258_ = lean_ctor_get(v_l_1241_, 4);
v_size_1259_ = lean_ctor_get(v_r_1242_, 0);
v___x_1260_ = lean_unsigned_to_nat(2u);
v___x_1261_ = lean_nat_mul(v___x_1260_, v_size_1259_);
v___x_1262_ = lean_nat_dec_lt(v_size_1254_, v___x_1261_);
lean_dec(v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1290_; 
lean_inc(v_r_1258_);
lean_inc(v_l_1257_);
lean_inc(v_v_1256_);
lean_inc(v_k_1255_);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_l_1241_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; lean_object* v_unused_1292_; lean_object* v_unused_1293_; lean_object* v_unused_1294_; lean_object* v_unused_1295_; 
v_unused_1291_ = lean_ctor_get(v_l_1241_, 4);
lean_dec(v_unused_1291_);
v_unused_1292_ = lean_ctor_get(v_l_1241_, 3);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v_l_1241_, 2);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v_l_1241_, 1);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v_l_1241_, 0);
lean_dec(v_unused_1295_);
v___x_1264_ = v_l_1241_;
v_isShared_1265_ = v_isSharedCheck_1290_;
goto v_resetjp_1263_;
}
else
{
lean_dec(v_l_1241_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1290_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1280_; 
v___x_1266_ = lean_nat_add(v___x_1236_, v_size_1237_);
v___x_1267_ = lean_nat_add(v___x_1266_, v_size_1238_);
lean_dec(v_size_1238_);
if (lean_obj_tag(v_l_1257_) == 0)
{
lean_object* v_size_1288_; 
v_size_1288_ = lean_ctor_get(v_l_1257_, 0);
lean_inc(v_size_1288_);
v___y_1280_ = v_size_1288_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_unsigned_to_nat(0u);
v___y_1280_ = v___x_1289_;
goto v___jp_1279_;
}
v___jp_1268_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = lean_nat_add(v___y_1269_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec(v___y_1269_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 4, v_r_1242_);
lean_ctor_set(v___x_1264_, 3, v_r_1258_);
lean_ctor_set(v___x_1264_, 2, v_v_1240_);
lean_ctor_set(v___x_1264_, 1, v_k_1239_);
lean_ctor_set(v___x_1264_, 0, v___x_1272_);
v___x_1274_ = v___x_1264_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_k_1239_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_v_1240_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_r_1258_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_r_1242_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v___x_1274_);
lean_ctor_set(v___x_1252_, 3, v___y_1270_);
lean_ctor_set(v___x_1252_, 2, v_v_1256_);
lean_ctor_set(v___x_1252_, 1, v_k_1255_);
lean_ctor_set(v___x_1252_, 0, v___x_1267_);
v___x_1276_ = v___x_1252_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1255_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1256_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v___y_1270_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_nat_add(v___x_1266_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec(v___x_1266_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v_l_1257_);
lean_ctor_set(v___x_1092_, 0, v___x_1281_);
v___x_1283_ = v___x_1092_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_l_1089_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_l_1257_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_nat_add(v___x_1236_, v_size_1259_);
if (lean_obj_tag(v_r_1258_) == 0)
{
lean_object* v_size_1285_; 
v_size_1285_ = lean_ctor_get(v_r_1258_, 0);
lean_inc(v_size_1285_);
v___y_1269_ = v___x_1284_;
v___y_1270_ = v___x_1283_;
v___y_1271_ = v_size_1285_;
goto v___jp_1268_;
}
else
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___y_1269_ = v___x_1284_;
v___y_1270_ = v___x_1283_;
v___y_1271_ = v___x_1286_;
goto v___jp_1268_;
}
}
}
}
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
lean_del_object(v___x_1092_);
v___x_1296_ = lean_nat_add(v___x_1236_, v_size_1237_);
v___x_1297_ = lean_nat_add(v___x_1296_, v_size_1238_);
lean_dec(v_size_1238_);
v___x_1298_ = lean_nat_add(v___x_1296_, v_size_1254_);
lean_dec(v___x_1296_);
lean_inc_ref(v_l_1089_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v_l_1241_);
lean_ctor_set(v___x_1252_, 3, v_l_1089_);
lean_ctor_set(v___x_1252_, 2, v_v_1088_);
lean_ctor_set(v___x_1252_, 1, v_k_1087_);
lean_ctor_set(v___x_1252_, 0, v___x_1298_);
v___x_1300_ = v___x_1252_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_l_1089_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v_l_1241_);
v___x_1300_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_isSharedCheck_1307_ = !lean_is_exclusive(v_l_1089_);
if (v_isSharedCheck_1307_ == 0)
{
lean_object* v_unused_1308_; lean_object* v_unused_1309_; lean_object* v_unused_1310_; lean_object* v_unused_1311_; lean_object* v_unused_1312_; 
v_unused_1308_ = lean_ctor_get(v_l_1089_, 4);
lean_dec(v_unused_1308_);
v_unused_1309_ = lean_ctor_get(v_l_1089_, 3);
lean_dec(v_unused_1309_);
v_unused_1310_ = lean_ctor_get(v_l_1089_, 2);
lean_dec(v_unused_1310_);
v_unused_1311_ = lean_ctor_get(v_l_1089_, 1);
lean_dec(v_unused_1311_);
v_unused_1312_ = lean_ctor_get(v_l_1089_, 0);
lean_dec(v_unused_1312_);
v___x_1302_ = v_l_1089_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_dec(v_l_1089_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 4, v_r_1242_);
lean_ctor_set(v___x_1302_, 3, v___x_1300_);
lean_ctor_set(v___x_1302_, 2, v_v_1240_);
lean_ctor_set(v___x_1302_, 1, v_k_1239_);
lean_ctor_set(v___x_1302_, 0, v___x_1297_);
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_k_1239_);
lean_ctor_set(v_reuseFailAlloc_1306_, 2, v_v_1240_);
lean_ctor_set(v_reuseFailAlloc_1306_, 3, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1306_, 4, v_r_1242_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1320_; 
v_l_1320_ = lean_ctor_get(v_impl_1235_, 3);
lean_inc(v_l_1320_);
if (lean_obj_tag(v_l_1320_) == 0)
{
lean_object* v_r_1321_; lean_object* v_k_1322_; lean_object* v_v_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1346_; 
v_r_1321_ = lean_ctor_get(v_impl_1235_, 4);
v_k_1322_ = lean_ctor_get(v_impl_1235_, 1);
v_v_1323_ = lean_ctor_get(v_impl_1235_, 2);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_impl_1235_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; lean_object* v_unused_1348_; 
v_unused_1347_ = lean_ctor_get(v_impl_1235_, 3);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v_impl_1235_, 0);
lean_dec(v_unused_1348_);
v___x_1325_ = v_impl_1235_;
v_isShared_1326_ = v_isSharedCheck_1346_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_r_1321_);
lean_inc(v_v_1323_);
lean_inc(v_k_1322_);
lean_dec(v_impl_1235_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1346_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v_k_1327_; lean_object* v_v_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1342_; 
v_k_1327_ = lean_ctor_get(v_l_1320_, 1);
v_v_1328_ = lean_ctor_get(v_l_1320_, 2);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_l_1320_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; lean_object* v_unused_1344_; lean_object* v_unused_1345_; 
v_unused_1343_ = lean_ctor_get(v_l_1320_, 4);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_l_1320_, 3);
lean_dec(v_unused_1344_);
v_unused_1345_ = lean_ctor_get(v_l_1320_, 0);
lean_dec(v_unused_1345_);
v___x_1330_ = v_l_1320_;
v_isShared_1331_ = v_isSharedCheck_1342_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_v_1328_);
lean_inc(v_k_1327_);
lean_dec(v_l_1320_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1342_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1321_, 2);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 4, v_r_1321_);
lean_ctor_set(v___x_1330_, 3, v_r_1321_);
lean_ctor_set(v___x_1330_, 2, v_v_1088_);
lean_ctor_set(v___x_1330_, 1, v_k_1087_);
lean_ctor_set(v___x_1330_, 0, v___x_1236_);
v___x_1334_ = v___x_1330_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_r_1321_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_r_1321_);
v___x_1334_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1336_; 
lean_inc(v_r_1321_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 3, v_r_1321_);
lean_ctor_set(v___x_1325_, 0, v___x_1236_);
v___x_1336_ = v___x_1325_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_k_1322_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_v_1323_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_r_1321_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_r_1321_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v___x_1336_);
lean_ctor_set(v___x_1092_, 3, v___x_1334_);
lean_ctor_set(v___x_1092_, 2, v_v_1328_);
lean_ctor_set(v___x_1092_, 1, v_k_1327_);
lean_ctor_set(v___x_1092_, 0, v___x_1332_);
v___x_1338_ = v___x_1092_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1327_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1328_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
else
{
lean_object* v_r_1349_; 
v_r_1349_ = lean_ctor_get(v_impl_1235_, 4);
lean_inc(v_r_1349_);
if (lean_obj_tag(v_r_1349_) == 0)
{
lean_object* v_k_1350_; lean_object* v_v_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1362_; 
v_k_1350_ = lean_ctor_get(v_impl_1235_, 1);
v_v_1351_ = lean_ctor_get(v_impl_1235_, 2);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_impl_1235_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; lean_object* v_unused_1364_; lean_object* v_unused_1365_; 
v_unused_1363_ = lean_ctor_get(v_impl_1235_, 4);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_impl_1235_, 3);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_impl_1235_, 0);
lean_dec(v_unused_1365_);
v___x_1353_ = v_impl_1235_;
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_v_1351_);
lean_inc(v_k_1350_);
lean_dec(v_impl_1235_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = lean_unsigned_to_nat(3u);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_l_1320_);
lean_ctor_set(v___x_1353_, 2, v_v_1088_);
lean_ctor_set(v___x_1353_, 1, v_k_1087_);
lean_ctor_set(v___x_1353_, 0, v___x_1236_);
v___x_1357_ = v___x_1353_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_l_1320_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v_l_1320_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1359_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v_r_1349_);
lean_ctor_set(v___x_1092_, 3, v___x_1357_);
lean_ctor_set(v___x_1092_, 2, v_v_1351_);
lean_ctor_set(v___x_1092_, 1, v_k_1350_);
lean_ctor_set(v___x_1092_, 0, v___x_1355_);
v___x_1359_ = v___x_1092_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_k_1350_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_v_1351_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v_r_1349_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_unsigned_to_nat(2u);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v_impl_1235_);
lean_ctor_set(v___x_1092_, 3, v_r_1349_);
lean_ctor_set(v___x_1092_, 0, v___x_1366_);
v___x_1368_ = v___x_1092_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_r_1349_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_impl_1235_);
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
}
}
}
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v_k_1083_);
lean_ctor_set(v___x_1372_, 2, v_v_1084_);
lean_ctor_set(v___x_1372_, 3, v_t_1085_);
lean_ctor_set(v___x_1372_, 4, v_t_1085_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1373_, lean_object* v_mvarId_1374_){
_start:
{
uint8_t v___x_1375_; 
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1374_, v_s_1373_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1374_, v___x_1376_, v_s_1373_);
return v___x_1377_;
}
else
{
lean_dec(v_mvarId_1374_);
return v_s_1373_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1378_, lean_object* v_k_1379_, lean_object* v_t_1380_){
_start:
{
uint8_t v___x_1381_; 
v___x_1381_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1379_, v_t_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1382_, lean_object* v_k_1383_, lean_object* v_t_1384_){
_start:
{
uint8_t v_res_1385_; lean_object* v_r_1386_; 
v_res_1385_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1382_, v_k_1383_, v_t_1384_);
lean_dec(v_t_1384_);
lean_dec(v_k_1383_);
v_r_1386_ = lean_box(v_res_1385_);
return v_r_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1387_, lean_object* v_k_1388_, lean_object* v_v_1389_, lean_object* v_t_1390_, lean_object* v_hl_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1388_, v_v_1389_, v_t_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1393_){
_start:
{
lean_object* v___f_1394_; lean_object* v___x_1395_; 
v___f_1394_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1395_ = l_Std_TreeSet_ofList___redArg(v_l_1393_, v___f_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_MVarIdSet_ofList(v_l_1396_);
lean_dec(v_l_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1398_){
_start:
{
lean_object* v___f_1399_; lean_object* v___x_1400_; 
v___f_1399_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1400_ = l_Std_TreeSet_ofArray___redArg(v_l_1398_, v___f_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_MVarIdSet_ofArray(v_l_1401_);
lean_dec_ref(v_l_1401_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1403_, lean_object* v_m_1404_, lean_object* v_init_1405_, lean_object* v_f_1406_){
_start:
{
lean_object* v_toApplicative_1407_; lean_object* v_toBind_1408_; lean_object* v_toPure_1409_; lean_object* v___f_1410_; lean_object* v___x_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; 
v_toApplicative_1407_ = lean_ctor_get(v_inst_1403_, 0);
v_toBind_1408_ = lean_ctor_get(v_inst_1403_, 1);
lean_inc(v_toBind_1408_);
v_toPure_1409_ = lean_ctor_get(v_toApplicative_1407_, 1);
lean_inc(v_toPure_1409_);
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1410_, 0, v_f_1406_);
v___x_1411_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1403_, v___f_1410_, v_init_1405_, v_m_1404_);
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1412_, 0, v_toPure_1409_);
v___x_1413_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1411_, v___f_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1414_, lean_object* v_inst_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_m_1417_, lean_object* v_init_1418_, lean_object* v_f_1419_){
_start:
{
lean_object* v_toApplicative_1420_; lean_object* v_toBind_1421_; lean_object* v_toPure_1422_; lean_object* v___f_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; 
v_toApplicative_1420_ = lean_ctor_get(v_inst_1415_, 0);
v_toBind_1421_ = lean_ctor_get(v_inst_1415_, 1);
lean_inc(v_toBind_1421_);
v_toPure_1422_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc(v_toPure_1422_);
v___f_1423_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1423_, 0, v_f_1419_);
v___x_1424_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1415_, v___f_1423_, v_init_1418_, v_m_1417_);
v___f_1425_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1425_, 0, v_toPure_1422_);
v___x_1426_ = lean_apply_4(v_toBind_1421_, lean_box(0), lean_box(0), v___x_1424_, v___f_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1428_, 0, lean_box(0));
lean_closure_set(v___x_1428_, 1, v_inst_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1429_, lean_object* v_inst_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1431_, 0, lean_box(0));
lean_closure_set(v___x_1431_, 1, v_inst_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1432_, lean_object* v_mvarId_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1433_, v_a_1434_, v_s_1432_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1436_, lean_object* v_s_1437_, lean_object* v_mvarId_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1438_, v_a_1439_, v_s_1437_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_box(1);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg();
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_box(1);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_box(1);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg___boxed(lean_object* v___dummy_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_instEmptyCollectionMVarIdMap___redArg();
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_box(1);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1453_, lean_object* v_a_1454_, lean_object* v_b_1455_, lean_object* v_c_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_a_1454_);
lean_ctor_set(v___x_1457_, 1, v_b_1455_);
v___x_1458_ = lean_apply_2(v_f_1453_, v___x_1457_, v_c_1456_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1459_, lean_object* v_m_1460_, lean_object* v_init_1461_, lean_object* v_f_1462_){
_start:
{
lean_object* v_toApplicative_1463_; lean_object* v_toBind_1464_; lean_object* v_toPure_1465_; lean_object* v___f_1466_; lean_object* v___x_1467_; lean_object* v___f_1468_; lean_object* v___x_1469_; 
v_toApplicative_1463_ = lean_ctor_get(v_inst_1459_, 0);
v_toBind_1464_ = lean_ctor_get(v_inst_1459_, 1);
lean_inc(v_toBind_1464_);
v_toPure_1465_ = lean_ctor_get(v_toApplicative_1463_, 1);
lean_inc(v_toPure_1465_);
v___f_1466_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1466_, 0, v_f_1462_);
v___x_1467_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1459_, v___f_1466_, v_init_1461_, v_m_1460_);
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1468_, 0, v_toPure_1465_);
v___x_1469_ = lean_apply_4(v_toBind_1464_, lean_box(0), lean_box(0), v___x_1467_, v___f_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1470_, lean_object* v_00_u03b1_1471_, lean_object* v_inst_1472_, lean_object* v_00_u03b2_1473_, lean_object* v_m_1474_, lean_object* v_init_1475_, lean_object* v_f_1476_){
_start:
{
lean_object* v_toApplicative_1477_; lean_object* v_toBind_1478_; lean_object* v_toPure_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; lean_object* v___f_1482_; lean_object* v___x_1483_; 
v_toApplicative_1477_ = lean_ctor_get(v_inst_1472_, 0);
v_toBind_1478_ = lean_ctor_get(v_inst_1472_, 1);
lean_inc(v_toBind_1478_);
v_toPure_1479_ = lean_ctor_get(v_toApplicative_1477_, 1);
lean_inc(v_toPure_1479_);
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1480_, 0, v_f_1476_);
v___x_1481_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1472_, v___f_1480_, v_init_1475_, v_m_1474_);
v___f_1482_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1482_, 0, v_toPure_1479_);
v___x_1483_ = lean_apply_4(v_toBind_1478_, lean_box(0), lean_box(0), v___x_1481_, v___f_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1484_){
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
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1486_, lean_object* v_00_u03b1_1487_, lean_object* v_inst_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1489_, 0, lean_box(0));
lean_closure_set(v___x_1489_, 1, lean_box(0));
lean_closure_set(v___x_1489_, 2, v_inst_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_box(1);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg___boxed(lean_object* v___dummy_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_instInhabitedMVarIdMap___redArg();
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_box(1);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl(lean_object* v_x_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_obj_tag_nat(v_x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl___boxed(lean_object* v_x_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Expr_ctorIdx___impl(v_x_1498_);
lean_dec_ref(v_x_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1500_, lean_object* v_k_1501_){
_start:
{
switch(lean_obj_tag(v_t_1500_))
{
case 4:
{
lean_object* v_declName_1502_; lean_object* v_us_1503_; lean_object* v___x_1504_; 
v_declName_1502_ = lean_ctor_get(v_t_1500_, 0);
lean_inc(v_declName_1502_);
v_us_1503_ = lean_ctor_get(v_t_1500_, 1);
lean_inc(v_us_1503_);
lean_dec_ref_known(v_t_1500_, 2);
v___x_1504_ = lean_apply_2(v_k_1501_, v_declName_1502_, v_us_1503_);
return v___x_1504_;
}
case 5:
{
lean_object* v_fn_1505_; lean_object* v_arg_1506_; lean_object* v___x_1507_; 
v_fn_1505_ = lean_ctor_get(v_t_1500_, 0);
lean_inc_ref(v_fn_1505_);
v_arg_1506_ = lean_ctor_get(v_t_1500_, 1);
lean_inc_ref(v_arg_1506_);
lean_dec_ref_known(v_t_1500_, 2);
v___x_1507_ = lean_apply_2(v_k_1501_, v_fn_1505_, v_arg_1506_);
return v___x_1507_;
}
case 6:
{
lean_object* v_binderName_1508_; lean_object* v_binderType_1509_; lean_object* v_body_1510_; uint8_t v_binderInfo_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_binderName_1508_ = lean_ctor_get(v_t_1500_, 0);
lean_inc(v_binderName_1508_);
v_binderType_1509_ = lean_ctor_get(v_t_1500_, 1);
lean_inc_ref(v_binderType_1509_);
v_body_1510_ = lean_ctor_get(v_t_1500_, 2);
lean_inc_ref(v_body_1510_);
v_binderInfo_1511_ = lean_ctor_get_uint8(v_t_1500_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1500_, 3);
v___x_1512_ = lean_box(v_binderInfo_1511_);
v___x_1513_ = lean_apply_4(v_k_1501_, v_binderName_1508_, v_binderType_1509_, v_body_1510_, v___x_1512_);
return v___x_1513_;
}
case 7:
{
lean_object* v_binderName_1514_; lean_object* v_binderType_1515_; lean_object* v_body_1516_; uint8_t v_binderInfo_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_binderName_1514_ = lean_ctor_get(v_t_1500_, 0);
lean_inc(v_binderName_1514_);
v_binderType_1515_ = lean_ctor_get(v_t_1500_, 1);
lean_inc_ref(v_binderType_1515_);
v_body_1516_ = lean_ctor_get(v_t_1500_, 2);
lean_inc_ref(v_body_1516_);
v_binderInfo_1517_ = lean_ctor_get_uint8(v_t_1500_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1500_, 3);
v___x_1518_ = lean_box(v_binderInfo_1517_);
v___x_1519_ = lean_apply_4(v_k_1501_, v_binderName_1514_, v_binderType_1515_, v_body_1516_, v___x_1518_);
return v___x_1519_;
}
case 8:
{
lean_object* v_declName_1520_; lean_object* v_type_1521_; lean_object* v_value_1522_; lean_object* v_body_1523_; uint8_t v_nondep_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_declName_1520_ = lean_ctor_get(v_t_1500_, 0);
lean_inc(v_declName_1520_);
v_type_1521_ = lean_ctor_get(v_t_1500_, 1);
lean_inc_ref(v_type_1521_);
v_value_1522_ = lean_ctor_get(v_t_1500_, 2);
lean_inc_ref(v_value_1522_);
v_body_1523_ = lean_ctor_get(v_t_1500_, 3);
lean_inc_ref(v_body_1523_);
v_nondep_1524_ = lean_ctor_get_uint8(v_t_1500_, sizeof(void*)*4);
lean_dec_ref_known(v_t_1500_, 4);
v___x_1525_ = lean_box(v_nondep_1524_);
v___x_1526_ = lean_apply_5(v_k_1501_, v_declName_1520_, v_type_1521_, v_value_1522_, v_body_1523_, v___x_1525_);
return v___x_1526_;
}
case 9:
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v_t_1500_, 0);
lean_inc_ref(v_a_1527_);
lean_dec_ref_known(v_t_1500_, 1);
v___x_1528_ = lean_apply_1(v_k_1501_, v_a_1527_);
return v___x_1528_;
}
case 10:
{
lean_object* v_data_1529_; lean_object* v_expr_1530_; lean_object* v___x_1531_; 
v_data_1529_ = lean_ctor_get(v_t_1500_, 0);
lean_inc(v_data_1529_);
v_expr_1530_ = lean_ctor_get(v_t_1500_, 1);
lean_inc_ref(v_expr_1530_);
lean_dec_ref_known(v_t_1500_, 2);
v___x_1531_ = lean_apply_2(v_k_1501_, v_data_1529_, v_expr_1530_);
return v___x_1531_;
}
case 11:
{
lean_object* v_typeName_1532_; lean_object* v_idx_1533_; lean_object* v_struct_1534_; lean_object* v___x_1535_; 
v_typeName_1532_ = lean_ctor_get(v_t_1500_, 0);
lean_inc(v_typeName_1532_);
v_idx_1533_ = lean_ctor_get(v_t_1500_, 1);
lean_inc(v_idx_1533_);
v_struct_1534_ = lean_ctor_get(v_t_1500_, 2);
lean_inc_ref(v_struct_1534_);
lean_dec_ref_known(v_t_1500_, 3);
v___x_1535_ = lean_apply_3(v_k_1501_, v_typeName_1532_, v_idx_1533_, v_struct_1534_);
return v___x_1535_;
}
default: 
{
lean_object* v_deBruijnIndex_1536_; lean_object* v___x_1537_; 
v_deBruijnIndex_1536_ = lean_ctor_get(v_t_1500_, 0);
lean_inc(v_deBruijnIndex_1536_);
lean_dec_ref(v_t_1500_);
v___x_1537_ = lean_apply_1(v_k_1501_, v_deBruijnIndex_1536_);
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1538_, lean_object* v_ctorIdx_1539_, lean_object* v_t_1540_, lean_object* v_h_1541_, lean_object* v_k_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Expr_ctorElim___redArg(v_t_1540_, v_k_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1544_, lean_object* v_ctorIdx_1545_, lean_object* v_t_1546_, lean_object* v_h_1547_, lean_object* v_k_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Expr_ctorElim(v_motive_1544_, v_ctorIdx_1545_, v_t_1546_, v_h_1547_, v_k_1548_);
lean_dec(v_ctorIdx_1545_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1550_, lean_object* v_bvar_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Expr_ctorElim___redArg(v_t_1550_, v_bvar_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1553_, lean_object* v_t_1554_, lean_object* v_h_1555_, lean_object* v_bvar_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Expr_ctorElim___redArg(v_t_1554_, v_bvar_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1558_, lean_object* v_fvar_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Expr_ctorElim___redArg(v_t_1558_, v_fvar_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1561_, lean_object* v_t_1562_, lean_object* v_h_1563_, lean_object* v_fvar_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Expr_ctorElim___redArg(v_t_1562_, v_fvar_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1566_, lean_object* v_mvar_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Expr_ctorElim___redArg(v_t_1566_, v_mvar_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1569_, lean_object* v_t_1570_, lean_object* v_h_1571_, lean_object* v_mvar_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Expr_ctorElim___redArg(v_t_1570_, v_mvar_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1574_, lean_object* v_sort_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Expr_ctorElim___redArg(v_t_1574_, v_sort_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1577_, lean_object* v_t_1578_, lean_object* v_h_1579_, lean_object* v_sort_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Expr_ctorElim___redArg(v_t_1578_, v_sort_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1582_, lean_object* v_const_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Expr_ctorElim___redArg(v_t_1582_, v_const_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1585_, lean_object* v_t_1586_, lean_object* v_h_1587_, lean_object* v_const_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Expr_ctorElim___redArg(v_t_1586_, v_const_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1590_, lean_object* v_app_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_Expr_ctorElim___redArg(v_t_1590_, v_app_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1593_, lean_object* v_t_1594_, lean_object* v_h_1595_, lean_object* v_app_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Expr_ctorElim___redArg(v_t_1594_, v_app_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1598_, lean_object* v_lam_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Expr_ctorElim___redArg(v_t_1598_, v_lam_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1601_, lean_object* v_t_1602_, lean_object* v_h_1603_, lean_object* v_lam_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Expr_ctorElim___redArg(v_t_1602_, v_lam_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1606_, lean_object* v_forallE_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Expr_ctorElim___redArg(v_t_1606_, v_forallE_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1609_, lean_object* v_t_1610_, lean_object* v_h_1611_, lean_object* v_forallE_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Expr_ctorElim___redArg(v_t_1610_, v_forallE_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1614_, lean_object* v_letE_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Expr_ctorElim___redArg(v_t_1614_, v_letE_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1617_, lean_object* v_t_1618_, lean_object* v_h_1619_, lean_object* v_letE_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Expr_ctorElim___redArg(v_t_1618_, v_letE_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1622_, lean_object* v_lit_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Expr_ctorElim___redArg(v_t_1622_, v_lit_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1625_, lean_object* v_t_1626_, lean_object* v_h_1627_, lean_object* v_lit_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Expr_ctorElim___redArg(v_t_1626_, v_lit_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1630_, lean_object* v_mdata_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Expr_ctorElim___redArg(v_t_1630_, v_mdata_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1633_, lean_object* v_t_1634_, lean_object* v_h_1635_, lean_object* v_mdata_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Expr_ctorElim___redArg(v_t_1634_, v_mdata_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1638_, lean_object* v_proj_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Expr_ctorElim___redArg(v_t_1638_, v_proj_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1641_, lean_object* v_t_1642_, lean_object* v_h_1643_, lean_object* v_proj_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Expr_ctorElim___redArg(v_t_1642_, v_proj_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1647_){
_start:
{
uint64_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = lean_expr_data(v_a_00___x40___internal___hyg_1647_);
lean_dec_ref(v_a_00___x40___internal___hyg_1647_);
v_r_1649_ = lean_box_uint64(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1650_, lean_object* v_bvar_1651_, lean_object* v_fvar_1652_, lean_object* v_mvar_1653_, lean_object* v_sort_1654_, lean_object* v_const_1655_, lean_object* v_app_1656_, lean_object* v_lam_1657_, lean_object* v_forallE_1658_, lean_object* v_letE_1659_, lean_object* v_lit_1660_, lean_object* v_mdata_1661_, lean_object* v_proj_1662_){
_start:
{
switch(lean_obj_tag(v_t_1650_))
{
case 0:
{
lean_object* v_deBruijnIndex_1663_; lean_object* v___x_1664_; 
lean_dec(v_proj_1662_);
lean_dec(v_mdata_1661_);
lean_dec(v_lit_1660_);
lean_dec(v_letE_1659_);
lean_dec(v_forallE_1658_);
lean_dec(v_lam_1657_);
lean_dec(v_app_1656_);
lean_dec(v_const_1655_);
lean_dec(v_sort_1654_);
lean_dec(v_mvar_1653_);
lean_dec(v_fvar_1652_);
v_deBruijnIndex_1663_ = lean_ctor_get(v_t_1650_, 0);
lean_inc(v_deBruijnIndex_1663_);
lean_dec_ref_known(v_t_1650_, 1);
v___x_1664_ = lean_apply_1(v_bvar_1651_, v_deBruijnIndex_1663_);
return v___x_1664_;
}
case 1:
{
lean_object* v_fvarId_1665_; lean_object* v___x_1666_; 
lean_dec(v_proj_1662_);
lean_dec(v_mdata_1661_);
lean_dec(v_lit_1660_);
lean_dec(v_letE_1659_);
lean_dec(v_forallE_1658_);
lean_dec(v_lam_1657_);
lean_dec(v_app_1656_);
lean_dec(v_const_1655_);
lean_dec(v_sort_1654_);
lean_dec(v_mvar_1653_);
lean_dec(v_bvar_1651_);
v_fvarId_1665_ = lean_ctor_get(v_t_1650_, 0);
lean_inc(v_fvarId_1665_);
lean_dec_ref_known(v_t_1650_, 1);
v___x_1666_ = lean_apply_1(v_fvar_1652_, v_fvarId_1665_);
return v___x_1666_;
}
case 2:
{
lean_object* v_mvarId_1667_; lean_object* v___x_1668_; 
lean_dec(v_proj_1662_);
lean_dec(v_mdata_1661_);
lean_dec(v_lit_1660_);
lean_dec(v_letE_1659_);
lean_dec(v_forallE_1658_);
lean_dec(v_lam_1657_);
lean_dec(v_app_1656_);
lean_dec(v_const_1655_);
lean_dec(v_sort_1654_);
lean_dec(v_fvar_1652_);
lean_dec(v_bvar_1651_);
v_mvarId_1667_ = lean_ctor_get(v_t_1650_, 0);
lean_inc(v_mvarId_1667_);
lean_dec_ref_known(v_t_1650_, 1);
v___x_1668_ = lean_apply_1(v_mvar_1653_, v_mvarId_1667_);
return v___x_1668_;
}
case 3:
{
lean_object* v_u_1669_; lean_object* v___x_1670_; 
lean_dec(v_proj_1662_);
lean_dec(v_mdata_1661_);
lean_dec(v_lit_1660_);
lean_dec(v_letE_1659_);
lean_dec(v_forallE_1658_);
lean_dec(v_lam_1657_);
lean_dec(v_app_1656_);
lean_dec(v_const_1655_);
lean_dec(v_mvar_1653_);
lean_dec(v_fvar_1652_);
lean_dec(v_bvar_1651_);
v_u_1669_ = lean_ctor_get(v_t_1650_, 0);
lean_inc(v_u_1669_);
lean_dec_ref_known(v_t_1650_, 1);
v___x_1670_ = lean_apply_1(v_sort_1654_, v_u_1669_);
return v___x_1670_;
}
case 4:
{
lean_object* v_declName_1671_; lean_object* v_us_1672_; lean_object* v___x_1673_; 
lean_dec(v_proj_1662_);
lean_dec(v_mdata_1661_);
lean_dec(v_lit_1660_);
lean_dec(v_letE_1659_);
lean_dec(v_forallE_1658_);
lean_dec(v_lam_1657_);
lean_dec(v_app_1656_);
lean_dec(v_sort_1654_);
lean_dec(v_mvar_1653_);
lean_dec(v_fvar_1652_);
lean_dec(v_bvar_1651_);
v_declName_1671_ = lean_ctor_get(v_t_1650_, 0);
lean_inc(v_declName_1671_);
v_us_1672_ = lean_ctor_get(v_t_1650_, 1);
lean_inc(v_us_1672_);
lean_dec_ref_known(v_t_1650_, 2);
v___x_1673_ = lean_apply_2(v_const_1655_, v_declName_1671_, v_us_1672_);
return v___x_1673_;
}
case 5:
{
lean_object* v_fn_1674_; lean_object* v_arg_1675_; lean_object* v___x_1676_; 
lean_dec(v_proj_1662_);
lean_dec(v_mdata_1661_);
lean_dec(v_lit_1660_);
lean_dec(v_letE_1659_);
lean_dec(v_forallE_1658_);
lean_dec(v_lam_1657_);
lean_dec(v_const_1655_);
lean_dec(v_sort_1654_);
lean_dec(v_mvar_1653_);
lean_dec(v_fvar_1652_);
lean_dec(v_bvar_1651_);
v_fn_1674_ = lean_ctor_get(v_t_1650_, 0);
lean_inc_ref(v_fn_1674_);
v_arg_1675_ = lean_ctor_get(v_t_1650_, 1);
lean_inc_ref(v_arg_1675_);
lean_dec_ref_known(v_t_1650_, 2);
v___x_1676_ = lean_apply_2(v_app_1656_, v_fn_1674_, v_arg_1675_);
return v___x_1676_;
}
case 6:
{
lean_object* v_binderName_1677_; lean_object* v_binderType_1678_; lean_object* v_body_1679_; uint8_t v_binderInfo_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec(v_proj_1662_);
lean_dec(v_mdata_1661_);
lean_dec(v_lit_1660_);
lean_dec(v_letE_1659_);
lean_dec(v_forallE_1658_);
lean_dec(v_app_1656_);
lean_dec(v_const_1655_);
lean_dec(v_sort_1654_);
lean_dec(v_mvar_1653_);
lean_dec(v_fvar_1652_);
lean_dec(v_bvar_1651_);
v_binderName_1677_ = lean_ctor_get(v_t_1650_, 0);
lean_inc(v_binderName_1677_);
v_binderType_1678_ = lean_ctor_get(v_t_1650_, 1);
lean_inc_ref(v_binderType_1678_);
v_body_1679_ = lean_ctor_get(v_t_1650_, 2);
lean_inc_ref(v_body_1679_);
v_binderInfo_1680_ = lean_ctor_get_uint8(v_t_1650_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1650_, 3);
v___x_1681_ = lean_box(v_binderInfo_1680_);
v___x_1682_ = lean_apply_4(v_lam_1657_, v_binderName_1677_, v_binderType_1678_, v_body_1679_, v___x_1681_);
return v___x_1682_;
}
case 7:
{
lean_object* v_binderName_1683_; lean_object* v_binderType_1684_; lean_object* v_body_1685_; uint8_t v_binderInfo_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_proj_1662_);
lean_dec(v_mdata_1661_);
lean_dec(v_lit_1660_);
lean_dec(v_letE_1659_);
lean_dec(v_lam_1657_);
lean_dec(v_app_1656_);
lean_dec(v_const_1655_);
lean_dec(v_sort_1654_);
lean_dec(v_mvar_1653_);
lean_dec(v_fvar_1652_);
lean_dec(v_bvar_1651_);
v_binderName_1683_ = lean_ctor_get(v_t_1650_, 0);
lean_inc(v_binderName_1683_);
v_binderType_1684_ = lean_ctor_get(v_t_1650_, 1);
lean_inc_ref(v_binderType_1684_);
v_body_1685_ = lean_ctor_get(v_t_1650_, 2);
lean_inc_ref(v_body_1685_);
v_binderInfo_1686_ = lean_ctor_get_uint8(v_t_1650_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1650_, 3);
v___x_1687_ = lean_box(v_binderInfo_1686_);
v___x_1688_ = lean_apply_4(v_forallE_1658_, v_binderName_1683_, v_binderType_1684_, v_body_1685_, v___x_1687_);
return v___x_1688_;
}
case 8:
{
lean_object* v_declName_1689_; lean_object* v_type_1690_; lean_object* v_value_1691_; lean_object* v_body_1692_; uint8_t v_nondep_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v_proj_1662_);
lean_dec(v_mdata_1661_);
lean_dec(v_lit_1660_);
lean_dec(v_forallE_1658_);
lean_dec(v_lam_1657_);
lean_dec(v_app_1656_);
lean_dec(v_const_1655_);
lean_dec(v_sort_1654_);
lean_dec(v_mvar_1653_);
lean_dec(v_fvar_1652_);
lean_dec(v_bvar_1651_);
v_declName_1689_ = lean_ctor_get(v_t_1650_, 0);
lean_inc(v_declName_1689_);
v_type_1690_ = lean_ctor_get(v_t_1650_, 1);
lean_inc_ref(v_type_1690_);
v_value_1691_ = lean_ctor_get(v_t_1650_, 2);
lean_inc_ref(v_value_1691_);
v_body_1692_ = lean_ctor_get(v_t_1650_, 3);
lean_inc_ref(v_body_1692_);
v_nondep_1693_ = lean_ctor_get_uint8(v_t_1650_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1650_, 4);
v___x_1694_ = lean_box(v_nondep_1693_);
v___x_1695_ = lean_apply_5(v_letE_1659_, v_declName_1689_, v_type_1690_, v_value_1691_, v_body_1692_, v___x_1694_);
return v___x_1695_;
}
case 9:
{
lean_object* v_a_1696_; lean_object* v___x_1697_; 
lean_dec(v_proj_1662_);
lean_dec(v_mdata_1661_);
lean_dec(v_letE_1659_);
lean_dec(v_forallE_1658_);
lean_dec(v_lam_1657_);
lean_dec(v_app_1656_);
lean_dec(v_const_1655_);
lean_dec(v_sort_1654_);
lean_dec(v_mvar_1653_);
lean_dec(v_fvar_1652_);
lean_dec(v_bvar_1651_);
v_a_1696_ = lean_ctor_get(v_t_1650_, 0);
lean_inc_ref(v_a_1696_);
lean_dec_ref_known(v_t_1650_, 1);
v___x_1697_ = lean_apply_1(v_lit_1660_, v_a_1696_);
return v___x_1697_;
}
case 10:
{
lean_object* v_data_1698_; lean_object* v_expr_1699_; lean_object* v___x_1700_; 
lean_dec(v_proj_1662_);
lean_dec(v_lit_1660_);
lean_dec(v_letE_1659_);
lean_dec(v_forallE_1658_);
lean_dec(v_lam_1657_);
lean_dec(v_app_1656_);
lean_dec(v_const_1655_);
lean_dec(v_sort_1654_);
lean_dec(v_mvar_1653_);
lean_dec(v_fvar_1652_);
lean_dec(v_bvar_1651_);
v_data_1698_ = lean_ctor_get(v_t_1650_, 0);
lean_inc(v_data_1698_);
v_expr_1699_ = lean_ctor_get(v_t_1650_, 1);
lean_inc_ref(v_expr_1699_);
lean_dec_ref_known(v_t_1650_, 2);
v___x_1700_ = lean_apply_2(v_mdata_1661_, v_data_1698_, v_expr_1699_);
return v___x_1700_;
}
default: 
{
lean_object* v_typeName_1701_; lean_object* v_idx_1702_; lean_object* v_struct_1703_; lean_object* v___x_1704_; 
lean_dec(v_mdata_1661_);
lean_dec(v_lit_1660_);
lean_dec(v_letE_1659_);
lean_dec(v_forallE_1658_);
lean_dec(v_lam_1657_);
lean_dec(v_app_1656_);
lean_dec(v_const_1655_);
lean_dec(v_sort_1654_);
lean_dec(v_mvar_1653_);
lean_dec(v_fvar_1652_);
lean_dec(v_bvar_1651_);
v_typeName_1701_ = lean_ctor_get(v_t_1650_, 0);
lean_inc(v_typeName_1701_);
v_idx_1702_ = lean_ctor_get(v_t_1650_, 1);
lean_inc(v_idx_1702_);
v_struct_1703_ = lean_ctor_get(v_t_1650_, 2);
lean_inc_ref(v_struct_1703_);
lean_dec_ref_known(v_t_1650_, 3);
v___x_1704_ = lean_apply_3(v_proj_1662_, v_typeName_1701_, v_idx_1702_, v_struct_1703_);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1705_, lean_object* v_t_1706_, lean_object* v_bvar_1707_, lean_object* v_fvar_1708_, lean_object* v_mvar_1709_, lean_object* v_sort_1710_, lean_object* v_const_1711_, lean_object* v_app_1712_, lean_object* v_lam_1713_, lean_object* v_forallE_1714_, lean_object* v_letE_1715_, lean_object* v_lit_1716_, lean_object* v_mdata_1717_, lean_object* v_proj_1718_){
_start:
{
switch(lean_obj_tag(v_t_1706_))
{
case 0:
{
lean_object* v_deBruijnIndex_1719_; lean_object* v___x_1720_; 
lean_dec(v_proj_1718_);
lean_dec(v_mdata_1717_);
lean_dec(v_lit_1716_);
lean_dec(v_letE_1715_);
lean_dec(v_forallE_1714_);
lean_dec(v_lam_1713_);
lean_dec(v_app_1712_);
lean_dec(v_const_1711_);
lean_dec(v_sort_1710_);
lean_dec(v_mvar_1709_);
lean_dec(v_fvar_1708_);
v_deBruijnIndex_1719_ = lean_ctor_get(v_t_1706_, 0);
lean_inc(v_deBruijnIndex_1719_);
lean_dec_ref_known(v_t_1706_, 1);
v___x_1720_ = lean_apply_1(v_bvar_1707_, v_deBruijnIndex_1719_);
return v___x_1720_;
}
case 1:
{
lean_object* v_fvarId_1721_; lean_object* v___x_1722_; 
lean_dec(v_proj_1718_);
lean_dec(v_mdata_1717_);
lean_dec(v_lit_1716_);
lean_dec(v_letE_1715_);
lean_dec(v_forallE_1714_);
lean_dec(v_lam_1713_);
lean_dec(v_app_1712_);
lean_dec(v_const_1711_);
lean_dec(v_sort_1710_);
lean_dec(v_mvar_1709_);
lean_dec(v_bvar_1707_);
v_fvarId_1721_ = lean_ctor_get(v_t_1706_, 0);
lean_inc(v_fvarId_1721_);
lean_dec_ref_known(v_t_1706_, 1);
v___x_1722_ = lean_apply_1(v_fvar_1708_, v_fvarId_1721_);
return v___x_1722_;
}
case 2:
{
lean_object* v_mvarId_1723_; lean_object* v___x_1724_; 
lean_dec(v_proj_1718_);
lean_dec(v_mdata_1717_);
lean_dec(v_lit_1716_);
lean_dec(v_letE_1715_);
lean_dec(v_forallE_1714_);
lean_dec(v_lam_1713_);
lean_dec(v_app_1712_);
lean_dec(v_const_1711_);
lean_dec(v_sort_1710_);
lean_dec(v_fvar_1708_);
lean_dec(v_bvar_1707_);
v_mvarId_1723_ = lean_ctor_get(v_t_1706_, 0);
lean_inc(v_mvarId_1723_);
lean_dec_ref_known(v_t_1706_, 1);
v___x_1724_ = lean_apply_1(v_mvar_1709_, v_mvarId_1723_);
return v___x_1724_;
}
case 3:
{
lean_object* v_u_1725_; lean_object* v___x_1726_; 
lean_dec(v_proj_1718_);
lean_dec(v_mdata_1717_);
lean_dec(v_lit_1716_);
lean_dec(v_letE_1715_);
lean_dec(v_forallE_1714_);
lean_dec(v_lam_1713_);
lean_dec(v_app_1712_);
lean_dec(v_const_1711_);
lean_dec(v_mvar_1709_);
lean_dec(v_fvar_1708_);
lean_dec(v_bvar_1707_);
v_u_1725_ = lean_ctor_get(v_t_1706_, 0);
lean_inc(v_u_1725_);
lean_dec_ref_known(v_t_1706_, 1);
v___x_1726_ = lean_apply_1(v_sort_1710_, v_u_1725_);
return v___x_1726_;
}
case 4:
{
lean_object* v_declName_1727_; lean_object* v_us_1728_; lean_object* v___x_1729_; 
lean_dec(v_proj_1718_);
lean_dec(v_mdata_1717_);
lean_dec(v_lit_1716_);
lean_dec(v_letE_1715_);
lean_dec(v_forallE_1714_);
lean_dec(v_lam_1713_);
lean_dec(v_app_1712_);
lean_dec(v_sort_1710_);
lean_dec(v_mvar_1709_);
lean_dec(v_fvar_1708_);
lean_dec(v_bvar_1707_);
v_declName_1727_ = lean_ctor_get(v_t_1706_, 0);
lean_inc(v_declName_1727_);
v_us_1728_ = lean_ctor_get(v_t_1706_, 1);
lean_inc(v_us_1728_);
lean_dec_ref_known(v_t_1706_, 2);
v___x_1729_ = lean_apply_2(v_const_1711_, v_declName_1727_, v_us_1728_);
return v___x_1729_;
}
case 5:
{
lean_object* v_fn_1730_; lean_object* v_arg_1731_; lean_object* v___x_1732_; 
lean_dec(v_proj_1718_);
lean_dec(v_mdata_1717_);
lean_dec(v_lit_1716_);
lean_dec(v_letE_1715_);
lean_dec(v_forallE_1714_);
lean_dec(v_lam_1713_);
lean_dec(v_const_1711_);
lean_dec(v_sort_1710_);
lean_dec(v_mvar_1709_);
lean_dec(v_fvar_1708_);
lean_dec(v_bvar_1707_);
v_fn_1730_ = lean_ctor_get(v_t_1706_, 0);
lean_inc_ref(v_fn_1730_);
v_arg_1731_ = lean_ctor_get(v_t_1706_, 1);
lean_inc_ref(v_arg_1731_);
lean_dec_ref_known(v_t_1706_, 2);
v___x_1732_ = lean_apply_2(v_app_1712_, v_fn_1730_, v_arg_1731_);
return v___x_1732_;
}
case 6:
{
lean_object* v_binderName_1733_; lean_object* v_binderType_1734_; lean_object* v_body_1735_; uint8_t v_binderInfo_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v_proj_1718_);
lean_dec(v_mdata_1717_);
lean_dec(v_lit_1716_);
lean_dec(v_letE_1715_);
lean_dec(v_forallE_1714_);
lean_dec(v_app_1712_);
lean_dec(v_const_1711_);
lean_dec(v_sort_1710_);
lean_dec(v_mvar_1709_);
lean_dec(v_fvar_1708_);
lean_dec(v_bvar_1707_);
v_binderName_1733_ = lean_ctor_get(v_t_1706_, 0);
lean_inc(v_binderName_1733_);
v_binderType_1734_ = lean_ctor_get(v_t_1706_, 1);
lean_inc_ref(v_binderType_1734_);
v_body_1735_ = lean_ctor_get(v_t_1706_, 2);
lean_inc_ref(v_body_1735_);
v_binderInfo_1736_ = lean_ctor_get_uint8(v_t_1706_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1706_, 3);
v___x_1737_ = lean_box(v_binderInfo_1736_);
v___x_1738_ = lean_apply_4(v_lam_1713_, v_binderName_1733_, v_binderType_1734_, v_body_1735_, v___x_1737_);
return v___x_1738_;
}
case 7:
{
lean_object* v_binderName_1739_; lean_object* v_binderType_1740_; lean_object* v_body_1741_; uint8_t v_binderInfo_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v_proj_1718_);
lean_dec(v_mdata_1717_);
lean_dec(v_lit_1716_);
lean_dec(v_letE_1715_);
lean_dec(v_lam_1713_);
lean_dec(v_app_1712_);
lean_dec(v_const_1711_);
lean_dec(v_sort_1710_);
lean_dec(v_mvar_1709_);
lean_dec(v_fvar_1708_);
lean_dec(v_bvar_1707_);
v_binderName_1739_ = lean_ctor_get(v_t_1706_, 0);
lean_inc(v_binderName_1739_);
v_binderType_1740_ = lean_ctor_get(v_t_1706_, 1);
lean_inc_ref(v_binderType_1740_);
v_body_1741_ = lean_ctor_get(v_t_1706_, 2);
lean_inc_ref(v_body_1741_);
v_binderInfo_1742_ = lean_ctor_get_uint8(v_t_1706_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1706_, 3);
v___x_1743_ = lean_box(v_binderInfo_1742_);
v___x_1744_ = lean_apply_4(v_forallE_1714_, v_binderName_1739_, v_binderType_1740_, v_body_1741_, v___x_1743_);
return v___x_1744_;
}
case 8:
{
lean_object* v_declName_1745_; lean_object* v_type_1746_; lean_object* v_value_1747_; lean_object* v_body_1748_; uint8_t v_nondep_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v_proj_1718_);
lean_dec(v_mdata_1717_);
lean_dec(v_lit_1716_);
lean_dec(v_forallE_1714_);
lean_dec(v_lam_1713_);
lean_dec(v_app_1712_);
lean_dec(v_const_1711_);
lean_dec(v_sort_1710_);
lean_dec(v_mvar_1709_);
lean_dec(v_fvar_1708_);
lean_dec(v_bvar_1707_);
v_declName_1745_ = lean_ctor_get(v_t_1706_, 0);
lean_inc(v_declName_1745_);
v_type_1746_ = lean_ctor_get(v_t_1706_, 1);
lean_inc_ref(v_type_1746_);
v_value_1747_ = lean_ctor_get(v_t_1706_, 2);
lean_inc_ref(v_value_1747_);
v_body_1748_ = lean_ctor_get(v_t_1706_, 3);
lean_inc_ref(v_body_1748_);
v_nondep_1749_ = lean_ctor_get_uint8(v_t_1706_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1706_, 4);
v___x_1750_ = lean_box(v_nondep_1749_);
v___x_1751_ = lean_apply_5(v_letE_1715_, v_declName_1745_, v_type_1746_, v_value_1747_, v_body_1748_, v___x_1750_);
return v___x_1751_;
}
case 9:
{
lean_object* v_a_1752_; lean_object* v___x_1753_; 
lean_dec(v_proj_1718_);
lean_dec(v_mdata_1717_);
lean_dec(v_letE_1715_);
lean_dec(v_forallE_1714_);
lean_dec(v_lam_1713_);
lean_dec(v_app_1712_);
lean_dec(v_const_1711_);
lean_dec(v_sort_1710_);
lean_dec(v_mvar_1709_);
lean_dec(v_fvar_1708_);
lean_dec(v_bvar_1707_);
v_a_1752_ = lean_ctor_get(v_t_1706_, 0);
lean_inc_ref(v_a_1752_);
lean_dec_ref_known(v_t_1706_, 1);
v___x_1753_ = lean_apply_1(v_lit_1716_, v_a_1752_);
return v___x_1753_;
}
case 10:
{
lean_object* v_data_1754_; lean_object* v_expr_1755_; lean_object* v___x_1756_; 
lean_dec(v_proj_1718_);
lean_dec(v_lit_1716_);
lean_dec(v_letE_1715_);
lean_dec(v_forallE_1714_);
lean_dec(v_lam_1713_);
lean_dec(v_app_1712_);
lean_dec(v_const_1711_);
lean_dec(v_sort_1710_);
lean_dec(v_mvar_1709_);
lean_dec(v_fvar_1708_);
lean_dec(v_bvar_1707_);
v_data_1754_ = lean_ctor_get(v_t_1706_, 0);
lean_inc(v_data_1754_);
v_expr_1755_ = lean_ctor_get(v_t_1706_, 1);
lean_inc_ref(v_expr_1755_);
lean_dec_ref_known(v_t_1706_, 2);
v___x_1756_ = lean_apply_2(v_mdata_1717_, v_data_1754_, v_expr_1755_);
return v___x_1756_;
}
default: 
{
lean_object* v_typeName_1757_; lean_object* v_idx_1758_; lean_object* v_struct_1759_; lean_object* v___x_1760_; 
lean_dec(v_mdata_1717_);
lean_dec(v_lit_1716_);
lean_dec(v_letE_1715_);
lean_dec(v_forallE_1714_);
lean_dec(v_lam_1713_);
lean_dec(v_app_1712_);
lean_dec(v_const_1711_);
lean_dec(v_sort_1710_);
lean_dec(v_mvar_1709_);
lean_dec(v_fvar_1708_);
lean_dec(v_bvar_1707_);
v_typeName_1757_ = lean_ctor_get(v_t_1706_, 0);
lean_inc(v_typeName_1757_);
v_idx_1758_ = lean_ctor_get(v_t_1706_, 1);
lean_inc(v_idx_1758_);
v_struct_1759_ = lean_ctor_get(v_t_1706_, 2);
lean_inc_ref(v_struct_1759_);
lean_dec_ref_known(v_t_1706_, 3);
v___x_1760_ = lean_apply_3(v_proj_1718_, v_typeName_1757_, v_idx_1758_, v_struct_1759_);
return v___x_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1761_){
_start:
{
uint64_t v___x_1762_; uint64_t v___x_1763_; uint64_t v___x_1764_; uint32_t v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint32_t v___x_1768_; uint8_t v___x_1769_; uint64_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1762_ = 7ULL;
v___x_1763_ = lean_uint64_of_nat(v_deBruijnIndex_1761_);
v___x_1764_ = lean_uint64_mix_hash(v___x_1762_, v___x_1763_);
v___x_1765_ = lean_uint64_to_uint32(v___x_1764_);
v___x_1766_ = lean_unsigned_to_nat(1u);
v___x_1767_ = lean_nat_add(v_deBruijnIndex_1761_, v___x_1766_);
v___x_1768_ = 0;
v___x_1769_ = 0;
v___x_1770_ = lean_expr_mk_data(v___x_1765_, v___x_1767_, v___x_1768_, v___x_1769_, v___x_1769_, v___x_1769_, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1771_, 0, v_deBruijnIndex_1761_);
lean_ctor_set_uint64(v___x_1771_, sizeof(void*)*1, v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1772_){
_start:
{
uint64_t v___x_1773_; uint64_t v___x_1774_; uint64_t v___x_1775_; uint32_t v___x_1776_; lean_object* v___x_1777_; uint32_t v___x_1778_; uint8_t v___x_1779_; uint8_t v___x_1780_; uint64_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1773_ = 13ULL;
v___x_1774_ = l_Lean_instHashableFVarId_hash(v_fvarId_1772_);
v___x_1775_ = lean_uint64_mix_hash(v___x_1773_, v___x_1774_);
v___x_1776_ = lean_uint64_to_uint32(v___x_1775_);
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = 0;
v___x_1779_ = 1;
v___x_1780_ = 0;
v___x_1781_ = lean_expr_mk_data(v___x_1776_, v___x_1777_, v___x_1778_, v___x_1779_, v___x_1780_, v___x_1780_, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1782_, 0, v_fvarId_1772_);
lean_ctor_set_uint64(v___x_1782_, sizeof(void*)*1, v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1783_){
_start:
{
uint64_t v___x_1784_; uint64_t v___x_1785_; uint64_t v___x_1786_; uint32_t v___x_1787_; lean_object* v___x_1788_; uint32_t v___x_1789_; uint8_t v___x_1790_; uint8_t v___x_1791_; uint64_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1784_ = 17ULL;
v___x_1785_ = l_Lean_instHashableMVarId_hash(v_mvarId_1783_);
v___x_1786_ = lean_uint64_mix_hash(v___x_1784_, v___x_1785_);
v___x_1787_ = lean_uint64_to_uint32(v___x_1786_);
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = 0;
v___x_1790_ = 0;
v___x_1791_ = 1;
v___x_1792_ = lean_expr_mk_data(v___x_1787_, v___x_1788_, v___x_1789_, v___x_1790_, v___x_1791_, v___x_1790_, v___x_1790_);
v___x_1793_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1793_, 0, v_mvarId_1783_);
lean_ctor_set_uint64(v___x_1793_, sizeof(void*)*1, v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1794_){
_start:
{
uint64_t v___x_1795_; uint64_t v___x_1796_; uint64_t v___x_1797_; uint32_t v___x_1798_; lean_object* v___x_1799_; uint32_t v___x_1800_; uint8_t v___x_1801_; uint8_t v___x_1802_; uint8_t v___x_1803_; uint64_t v___x_1804_; lean_object* v___x_1805_; 
v___x_1795_ = 11ULL;
v___x_1796_ = l_Lean_Level_hash(v_u_1794_);
v___x_1797_ = lean_uint64_mix_hash(v___x_1795_, v___x_1796_);
v___x_1798_ = lean_uint64_to_uint32(v___x_1797_);
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = 0;
v___x_1801_ = 0;
v___x_1802_ = l_Lean_Level_hasMVar(v_u_1794_);
v___x_1803_ = l_Lean_Level_hasParam(v_u_1794_);
v___x_1804_ = lean_expr_mk_data(v___x_1798_, v___x_1799_, v___x_1800_, v___x_1801_, v___x_1801_, v___x_1802_, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1805_, 0, v_u_1794_);
lean_ctor_set_uint64(v___x_1805_, sizeof(void*)*1, v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1806_, lean_object* v_arg_1807_){
_start:
{
uint64_t v___x_1808_; uint64_t v___x_1809_; uint64_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1808_ = lean_expr_data(v_fn_1806_);
v___x_1809_ = lean_expr_data(v_arg_1807_);
v___x_1810_ = lean_expr_mk_app_data(v___x_1808_, v___x_1809_);
v___x_1811_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1811_, 0, v_fn_1806_);
lean_ctor_set(v___x_1811_, 1, v_arg_1807_);
lean_ctor_set_uint64(v___x_1811_, sizeof(void*)*2, v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1812_, lean_object* v_binderType_1813_, lean_object* v_body_1814_, uint8_t v_binderInfo_1815_){
_start:
{
uint32_t v___x_1816_; uint64_t v___x_1817_; uint32_t v___x_1818_; uint32_t v___x_1819_; uint64_t v___x_1820_; uint32_t v___x_1821_; uint32_t v___x_1822_; uint8_t v___y_1824_; uint8_t v___y_1825_; uint32_t v___y_1826_; lean_object* v___y_1827_; uint8_t v___y_1828_; uint8_t v___y_1829_; uint8_t v___y_1833_; lean_object* v___y_1834_; uint32_t v___y_1835_; uint8_t v___y_1836_; uint8_t v___y_1837_; uint8_t v___y_1841_; uint32_t v___y_1842_; lean_object* v___y_1843_; uint8_t v___y_1844_; lean_object* v___y_1848_; uint32_t v___y_1849_; uint8_t v___y_1850_; lean_object* v___y_1854_; uint32_t v___y_1855_; lean_object* v___y_1861_; uint32_t v___x_1867_; lean_object* v___x_1868_; uint32_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1816_ = 29;
v___x_1817_ = lean_expr_data(v_binderType_1813_);
v___x_1818_ = lean_uint64_to_uint32(v___x_1817_);
v___x_1819_ = lean_uint32_mix_hash(v___x_1816_, v___x_1818_);
v___x_1820_ = lean_expr_data(v_body_1814_);
v___x_1821_ = lean_uint64_to_uint32(v___x_1820_);
v___x_1822_ = lean_uint32_mix_hash(v___x_1819_, v___x_1821_);
v___x_1867_ = l_Lean_Expr_Data_looseBVarRange(v___x_1817_);
v___x_1868_ = lean_uint32_to_nat(v___x_1867_);
v___x_1869_ = l_Lean_Expr_Data_looseBVarRange(v___x_1820_);
v___x_1870_ = lean_uint32_to_nat(v___x_1869_);
v___x_1871_ = lean_unsigned_to_nat(1u);
v___x_1872_ = lean_nat_sub(v___x_1870_, v___x_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_nat_dec_le(v___x_1868_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_dec(v___x_1872_);
v___y_1861_ = v___x_1868_;
goto v___jp_1860_;
}
else
{
lean_dec(v___x_1868_);
v___y_1861_ = v___x_1872_;
goto v___jp_1860_;
}
v___jp_1823_:
{
uint64_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_expr_mk_data(v___x_1822_, v___y_1827_, v___y_1826_, v___y_1825_, v___y_1828_, v___y_1824_, v___y_1829_);
v___x_1831_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1831_, 0, v_binderName_1812_);
lean_ctor_set(v___x_1831_, 1, v_binderType_1813_);
lean_ctor_set(v___x_1831_, 2, v_body_1814_);
lean_ctor_set_uint64(v___x_1831_, sizeof(void*)*3, v___x_1830_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 8, v_binderInfo_1815_);
return v___x_1831_;
}
v___jp_1832_:
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Lean_Expr_Data_hasLevelParam(v___x_1817_);
if (v___x_1838_ == 0)
{
uint8_t v___x_1839_; 
v___x_1839_ = l_Lean_Expr_Data_hasLevelParam(v___x_1820_);
v___y_1824_ = v___y_1837_;
v___y_1825_ = v___y_1833_;
v___y_1826_ = v___y_1835_;
v___y_1827_ = v___y_1834_;
v___y_1828_ = v___y_1836_;
v___y_1829_ = v___x_1839_;
goto v___jp_1823_;
}
else
{
v___y_1824_ = v___y_1837_;
v___y_1825_ = v___y_1833_;
v___y_1826_ = v___y_1835_;
v___y_1827_ = v___y_1834_;
v___y_1828_ = v___y_1836_;
v___y_1829_ = v___x_1838_;
goto v___jp_1823_;
}
}
v___jp_1840_:
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1817_);
if (v___x_1845_ == 0)
{
uint8_t v___x_1846_; 
v___x_1846_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1820_);
v___y_1833_ = v___y_1841_;
v___y_1834_ = v___y_1843_;
v___y_1835_ = v___y_1842_;
v___y_1836_ = v___y_1844_;
v___y_1837_ = v___x_1846_;
goto v___jp_1832_;
}
else
{
v___y_1833_ = v___y_1841_;
v___y_1834_ = v___y_1843_;
v___y_1835_ = v___y_1842_;
v___y_1836_ = v___y_1844_;
v___y_1837_ = v___x_1845_;
goto v___jp_1832_;
}
}
v___jp_1847_:
{
uint8_t v___x_1851_; 
v___x_1851_ = l_Lean_Expr_Data_hasExprMVar(v___x_1817_);
if (v___x_1851_ == 0)
{
uint8_t v___x_1852_; 
v___x_1852_ = l_Lean_Expr_Data_hasExprMVar(v___x_1820_);
v___y_1841_ = v___y_1850_;
v___y_1842_ = v___y_1849_;
v___y_1843_ = v___y_1848_;
v___y_1844_ = v___x_1852_;
goto v___jp_1840_;
}
else
{
v___y_1841_ = v___y_1850_;
v___y_1842_ = v___y_1849_;
v___y_1843_ = v___y_1848_;
v___y_1844_ = v___x_1851_;
goto v___jp_1840_;
}
}
v___jp_1853_:
{
uint32_t v___x_1856_; uint32_t v___x_1857_; uint8_t v___x_1858_; 
v___x_1856_ = 1;
v___x_1857_ = lean_uint32_add(v___y_1855_, v___x_1856_);
v___x_1858_ = l_Lean_Expr_Data_hasFVar(v___x_1817_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; 
v___x_1859_ = l_Lean_Expr_Data_hasFVar(v___x_1820_);
v___y_1848_ = v___y_1854_;
v___y_1849_ = v___x_1857_;
v___y_1850_ = v___x_1859_;
goto v___jp_1847_;
}
else
{
v___y_1848_ = v___y_1854_;
v___y_1849_ = v___x_1857_;
v___y_1850_ = v___x_1858_;
goto v___jp_1847_;
}
}
v___jp_1860_:
{
uint8_t v___x_1862_; uint32_t v___x_1863_; uint8_t v___x_1864_; uint32_t v___x_1865_; uint8_t v___x_1866_; 
v___x_1862_ = l_Lean_Expr_Data_approxDepth(v___x_1817_);
v___x_1863_ = lean_uint8_to_uint32(v___x_1862_);
v___x_1864_ = l_Lean_Expr_Data_approxDepth(v___x_1820_);
v___x_1865_ = lean_uint8_to_uint32(v___x_1864_);
v___x_1866_ = lean_uint32_dec_le(v___x_1863_, v___x_1865_);
if (v___x_1866_ == 0)
{
v___y_1854_ = v___y_1861_;
v___y_1855_ = v___x_1863_;
goto v___jp_1853_;
}
else
{
v___y_1854_ = v___y_1861_;
v___y_1855_ = v___x_1865_;
goto v___jp_1853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1874_, lean_object* v_binderType_1875_, lean_object* v_body_1876_, lean_object* v_binderInfo_1877_){
_start:
{
uint8_t v_binderInfo_boxed_1878_; lean_object* v_res_1879_; 
v_binderInfo_boxed_1878_ = lean_unbox(v_binderInfo_1877_);
v_res_1879_ = l_Lean_Expr_lam___override(v_binderName_1874_, v_binderType_1875_, v_body_1876_, v_binderInfo_boxed_1878_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1880_, lean_object* v_binderType_1881_, lean_object* v_body_1882_, uint8_t v_binderInfo_1883_){
_start:
{
uint32_t v___x_1884_; uint64_t v___x_1885_; uint32_t v___x_1886_; uint32_t v___x_1887_; uint64_t v___x_1888_; uint32_t v___x_1889_; uint32_t v___x_1890_; lean_object* v___y_1892_; uint8_t v___y_1893_; uint8_t v___y_1894_; uint32_t v___y_1895_; uint8_t v___y_1896_; uint8_t v___y_1897_; lean_object* v___y_1901_; uint8_t v___y_1902_; uint8_t v___y_1903_; uint32_t v___y_1904_; uint8_t v___y_1905_; lean_object* v___y_1909_; uint8_t v___y_1910_; uint32_t v___y_1911_; uint8_t v___y_1912_; lean_object* v___y_1916_; uint32_t v___y_1917_; uint8_t v___y_1918_; lean_object* v___y_1922_; uint32_t v___y_1923_; lean_object* v___y_1929_; uint32_t v___x_1935_; lean_object* v___x_1936_; uint32_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1884_ = 31;
v___x_1885_ = lean_expr_data(v_binderType_1881_);
v___x_1886_ = lean_uint64_to_uint32(v___x_1885_);
v___x_1887_ = lean_uint32_mix_hash(v___x_1884_, v___x_1886_);
v___x_1888_ = lean_expr_data(v_body_1882_);
v___x_1889_ = lean_uint64_to_uint32(v___x_1888_);
v___x_1890_ = lean_uint32_mix_hash(v___x_1887_, v___x_1889_);
v___x_1935_ = l_Lean_Expr_Data_looseBVarRange(v___x_1885_);
v___x_1936_ = lean_uint32_to_nat(v___x_1935_);
v___x_1937_ = l_Lean_Expr_Data_looseBVarRange(v___x_1888_);
v___x_1938_ = lean_uint32_to_nat(v___x_1937_);
v___x_1939_ = lean_unsigned_to_nat(1u);
v___x_1940_ = lean_nat_sub(v___x_1938_, v___x_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_nat_dec_le(v___x_1936_, v___x_1940_);
if (v___x_1941_ == 0)
{
lean_dec(v___x_1940_);
v___y_1929_ = v___x_1936_;
goto v___jp_1928_;
}
else
{
lean_dec(v___x_1936_);
v___y_1929_ = v___x_1940_;
goto v___jp_1928_;
}
v___jp_1891_:
{
uint64_t v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_expr_mk_data(v___x_1890_, v___y_1892_, v___y_1895_, v___y_1894_, v___y_1893_, v___y_1896_, v___y_1897_);
v___x_1899_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1899_, 0, v_binderName_1880_);
lean_ctor_set(v___x_1899_, 1, v_binderType_1881_);
lean_ctor_set(v___x_1899_, 2, v_body_1882_);
lean_ctor_set_uint64(v___x_1899_, sizeof(void*)*3, v___x_1898_);
lean_ctor_set_uint8(v___x_1899_, sizeof(void*)*3 + 8, v_binderInfo_1883_);
return v___x_1899_;
}
v___jp_1900_:
{
uint8_t v___x_1906_; 
v___x_1906_ = l_Lean_Expr_Data_hasLevelParam(v___x_1885_);
if (v___x_1906_ == 0)
{
uint8_t v___x_1907_; 
v___x_1907_ = l_Lean_Expr_Data_hasLevelParam(v___x_1888_);
v___y_1892_ = v___y_1901_;
v___y_1893_ = v___y_1902_;
v___y_1894_ = v___y_1903_;
v___y_1895_ = v___y_1904_;
v___y_1896_ = v___y_1905_;
v___y_1897_ = v___x_1907_;
goto v___jp_1891_;
}
else
{
v___y_1892_ = v___y_1901_;
v___y_1893_ = v___y_1902_;
v___y_1894_ = v___y_1903_;
v___y_1895_ = v___y_1904_;
v___y_1896_ = v___y_1905_;
v___y_1897_ = v___x_1906_;
goto v___jp_1891_;
}
}
v___jp_1908_:
{
uint8_t v___x_1913_; 
v___x_1913_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1885_);
if (v___x_1913_ == 0)
{
uint8_t v___x_1914_; 
v___x_1914_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1888_);
v___y_1901_ = v___y_1909_;
v___y_1902_ = v___y_1912_;
v___y_1903_ = v___y_1910_;
v___y_1904_ = v___y_1911_;
v___y_1905_ = v___x_1914_;
goto v___jp_1900_;
}
else
{
v___y_1901_ = v___y_1909_;
v___y_1902_ = v___y_1912_;
v___y_1903_ = v___y_1910_;
v___y_1904_ = v___y_1911_;
v___y_1905_ = v___x_1913_;
goto v___jp_1900_;
}
}
v___jp_1915_:
{
uint8_t v___x_1919_; 
v___x_1919_ = l_Lean_Expr_Data_hasExprMVar(v___x_1885_);
if (v___x_1919_ == 0)
{
uint8_t v___x_1920_; 
v___x_1920_ = l_Lean_Expr_Data_hasExprMVar(v___x_1888_);
v___y_1909_ = v___y_1916_;
v___y_1910_ = v___y_1918_;
v___y_1911_ = v___y_1917_;
v___y_1912_ = v___x_1920_;
goto v___jp_1908_;
}
else
{
v___y_1909_ = v___y_1916_;
v___y_1910_ = v___y_1918_;
v___y_1911_ = v___y_1917_;
v___y_1912_ = v___x_1919_;
goto v___jp_1908_;
}
}
v___jp_1921_:
{
uint32_t v___x_1924_; uint32_t v___x_1925_; uint8_t v___x_1926_; 
v___x_1924_ = 1;
v___x_1925_ = lean_uint32_add(v___y_1923_, v___x_1924_);
v___x_1926_ = l_Lean_Expr_Data_hasFVar(v___x_1885_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; 
v___x_1927_ = l_Lean_Expr_Data_hasFVar(v___x_1888_);
v___y_1916_ = v___y_1922_;
v___y_1917_ = v___x_1925_;
v___y_1918_ = v___x_1927_;
goto v___jp_1915_;
}
else
{
v___y_1916_ = v___y_1922_;
v___y_1917_ = v___x_1925_;
v___y_1918_ = v___x_1926_;
goto v___jp_1915_;
}
}
v___jp_1928_:
{
uint8_t v___x_1930_; uint32_t v___x_1931_; uint8_t v___x_1932_; uint32_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1930_ = l_Lean_Expr_Data_approxDepth(v___x_1885_);
v___x_1931_ = lean_uint8_to_uint32(v___x_1930_);
v___x_1932_ = l_Lean_Expr_Data_approxDepth(v___x_1888_);
v___x_1933_ = lean_uint8_to_uint32(v___x_1932_);
v___x_1934_ = lean_uint32_dec_le(v___x_1931_, v___x_1933_);
if (v___x_1934_ == 0)
{
v___y_1922_ = v___y_1929_;
v___y_1923_ = v___x_1931_;
goto v___jp_1921_;
}
else
{
v___y_1922_ = v___y_1929_;
v___y_1923_ = v___x_1933_;
goto v___jp_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1942_, lean_object* v_binderType_1943_, lean_object* v_body_1944_, lean_object* v_binderInfo_1945_){
_start:
{
uint8_t v_binderInfo_boxed_1946_; lean_object* v_res_1947_; 
v_binderInfo_boxed_1946_ = lean_unbox(v_binderInfo_1945_);
v_res_1947_ = l_Lean_Expr_forallE___override(v_binderName_1942_, v_binderType_1943_, v_body_1944_, v_binderInfo_boxed_1946_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1948_, lean_object* v_type_1949_, lean_object* v_value_1950_, lean_object* v_body_1951_, uint8_t v_nondep_1952_){
_start:
{
uint32_t v___y_1954_; uint8_t v___y_1955_; uint32_t v___y_1956_; uint8_t v___y_1957_; uint8_t v___y_1958_; lean_object* v___y_1959_; uint8_t v___y_1960_; uint8_t v___x_1963_; uint32_t v___y_1965_; uint64_t v___y_1966_; uint8_t v___y_1967_; uint32_t v___y_1968_; uint64_t v___y_1969_; uint64_t v___y_1970_; uint8_t v___y_1971_; lean_object* v___y_1972_; uint8_t v___y_1973_; uint32_t v___y_1978_; uint64_t v___y_1979_; uint32_t v___y_1980_; uint64_t v___y_1981_; uint8_t v___y_1982_; uint64_t v___y_1983_; lean_object* v___y_1984_; uint8_t v___y_1985_; uint32_t v___y_1990_; uint64_t v___y_1991_; uint32_t v___y_1992_; uint64_t v___y_1993_; uint64_t v___y_1994_; lean_object* v___y_1995_; uint8_t v___y_1996_; uint64_t v___y_2001_; uint32_t v___y_2002_; uint64_t v___y_2003_; uint64_t v___y_2004_; lean_object* v___y_2005_; uint32_t v___y_2006_; uint64_t v___y_2013_; uint32_t v___y_2014_; uint64_t v___y_2015_; uint64_t v___y_2016_; lean_object* v___y_2017_; uint32_t v___y_2018_; uint64_t v___y_2023_; uint32_t v___y_2024_; uint64_t v___y_2025_; uint64_t v___y_2026_; lean_object* v___y_2027_; uint64_t v___y_2034_; uint32_t v___y_2035_; uint64_t v___y_2036_; uint64_t v___y_2037_; lean_object* v___y_2038_; uint32_t v___y_2045_; 
v___x_1963_ = 1;
if (v_nondep_1952_ == 0)
{
uint32_t v___x_2060_; 
v___x_2060_ = 37;
v___y_2045_ = v___x_2060_;
goto v___jp_2044_;
}
else
{
uint32_t v___x_2061_; 
v___x_2061_ = 41;
v___y_2045_ = v___x_2061_;
goto v___jp_2044_;
}
v___jp_1953_:
{
uint64_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_expr_mk_data(v___y_1956_, v___y_1959_, v___y_1954_, v___y_1958_, v___y_1955_, v___y_1957_, v___y_1960_);
v___x_1962_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1962_, 0, v_declName_1948_);
lean_ctor_set(v___x_1962_, 1, v_type_1949_);
lean_ctor_set(v___x_1962_, 2, v_value_1950_);
lean_ctor_set(v___x_1962_, 3, v_body_1951_);
lean_ctor_set_uint64(v___x_1962_, sizeof(void*)*4, v___x_1961_);
lean_ctor_set_uint8(v___x_1962_, sizeof(void*)*4 + 8, v_nondep_1952_);
return v___x_1962_;
}
v___jp_1964_:
{
uint8_t v___x_1974_; 
v___x_1974_ = l_Lean_Expr_Data_hasLevelParam(v___y_1970_);
if (v___x_1974_ == 0)
{
uint8_t v___x_1975_; 
v___x_1975_ = l_Lean_Expr_Data_hasLevelParam(v___y_1969_);
if (v___x_1975_ == 0)
{
uint8_t v___x_1976_; 
v___x_1976_ = l_Lean_Expr_Data_hasLevelParam(v___y_1966_);
v___y_1954_ = v___y_1965_;
v___y_1955_ = v___y_1967_;
v___y_1956_ = v___y_1968_;
v___y_1957_ = v___y_1973_;
v___y_1958_ = v___y_1971_;
v___y_1959_ = v___y_1972_;
v___y_1960_ = v___x_1976_;
goto v___jp_1953_;
}
else
{
v___y_1954_ = v___y_1965_;
v___y_1955_ = v___y_1967_;
v___y_1956_ = v___y_1968_;
v___y_1957_ = v___y_1973_;
v___y_1958_ = v___y_1971_;
v___y_1959_ = v___y_1972_;
v___y_1960_ = v___x_1963_;
goto v___jp_1953_;
}
}
else
{
v___y_1954_ = v___y_1965_;
v___y_1955_ = v___y_1967_;
v___y_1956_ = v___y_1968_;
v___y_1957_ = v___y_1973_;
v___y_1958_ = v___y_1971_;
v___y_1959_ = v___y_1972_;
v___y_1960_ = v___x_1963_;
goto v___jp_1953_;
}
}
v___jp_1977_:
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Lean_Expr_Data_hasLevelMVar(v___y_1983_);
if (v___x_1986_ == 0)
{
uint8_t v___x_1987_; 
v___x_1987_ = l_Lean_Expr_Data_hasLevelMVar(v___y_1981_);
if (v___x_1987_ == 0)
{
uint8_t v___x_1988_; 
v___x_1988_ = l_Lean_Expr_Data_hasLevelMVar(v___y_1979_);
v___y_1965_ = v___y_1978_;
v___y_1966_ = v___y_1979_;
v___y_1967_ = v___y_1985_;
v___y_1968_ = v___y_1980_;
v___y_1969_ = v___y_1981_;
v___y_1970_ = v___y_1983_;
v___y_1971_ = v___y_1982_;
v___y_1972_ = v___y_1984_;
v___y_1973_ = v___x_1988_;
goto v___jp_1964_;
}
else
{
v___y_1965_ = v___y_1978_;
v___y_1966_ = v___y_1979_;
v___y_1967_ = v___y_1985_;
v___y_1968_ = v___y_1980_;
v___y_1969_ = v___y_1981_;
v___y_1970_ = v___y_1983_;
v___y_1971_ = v___y_1982_;
v___y_1972_ = v___y_1984_;
v___y_1973_ = v___x_1963_;
goto v___jp_1964_;
}
}
else
{
v___y_1965_ = v___y_1978_;
v___y_1966_ = v___y_1979_;
v___y_1967_ = v___y_1985_;
v___y_1968_ = v___y_1980_;
v___y_1969_ = v___y_1981_;
v___y_1970_ = v___y_1983_;
v___y_1971_ = v___y_1982_;
v___y_1972_ = v___y_1984_;
v___y_1973_ = v___x_1963_;
goto v___jp_1964_;
}
}
v___jp_1989_:
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Lean_Expr_Data_hasExprMVar(v___y_1994_);
if (v___x_1997_ == 0)
{
uint8_t v___x_1998_; 
v___x_1998_ = l_Lean_Expr_Data_hasExprMVar(v___y_1993_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; 
v___x_1999_ = l_Lean_Expr_Data_hasExprMVar(v___y_1991_);
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1991_;
v___y_1980_ = v___y_1992_;
v___y_1981_ = v___y_1993_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v___y_1985_ = v___x_1999_;
goto v___jp_1977_;
}
else
{
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1991_;
v___y_1980_ = v___y_1992_;
v___y_1981_ = v___y_1993_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v___y_1985_ = v___x_1963_;
goto v___jp_1977_;
}
}
else
{
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1991_;
v___y_1980_ = v___y_1992_;
v___y_1981_ = v___y_1993_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v___y_1985_ = v___x_1963_;
goto v___jp_1977_;
}
}
v___jp_2000_:
{
uint32_t v___x_2007_; uint32_t v___x_2008_; uint8_t v___x_2009_; 
v___x_2007_ = 1;
v___x_2008_ = lean_uint32_add(v___y_2006_, v___x_2007_);
v___x_2009_ = l_Lean_Expr_Data_hasFVar(v___y_2004_);
if (v___x_2009_ == 0)
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Lean_Expr_Data_hasFVar(v___y_2003_);
if (v___x_2010_ == 0)
{
uint8_t v___x_2011_; 
v___x_2011_ = l_Lean_Expr_Data_hasFVar(v___y_2001_);
v___y_1990_ = v___x_2008_;
v___y_1991_ = v___y_2001_;
v___y_1992_ = v___y_2002_;
v___y_1993_ = v___y_2003_;
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___y_2005_;
v___y_1996_ = v___x_2011_;
goto v___jp_1989_;
}
else
{
v___y_1990_ = v___x_2008_;
v___y_1991_ = v___y_2001_;
v___y_1992_ = v___y_2002_;
v___y_1993_ = v___y_2003_;
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___y_2005_;
v___y_1996_ = v___x_1963_;
goto v___jp_1989_;
}
}
else
{
v___y_1990_ = v___x_2008_;
v___y_1991_ = v___y_2001_;
v___y_1992_ = v___y_2002_;
v___y_1993_ = v___y_2003_;
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___y_2005_;
v___y_1996_ = v___x_1963_;
goto v___jp_1989_;
}
}
v___jp_2012_:
{
uint8_t v___x_2019_; uint32_t v___x_2020_; uint8_t v___x_2021_; 
v___x_2019_ = l_Lean_Expr_Data_approxDepth(v___y_2013_);
v___x_2020_ = lean_uint8_to_uint32(v___x_2019_);
v___x_2021_ = lean_uint32_dec_le(v___y_2018_, v___x_2020_);
if (v___x_2021_ == 0)
{
v___y_2001_ = v___y_2013_;
v___y_2002_ = v___y_2014_;
v___y_2003_ = v___y_2015_;
v___y_2004_ = v___y_2016_;
v___y_2005_ = v___y_2017_;
v___y_2006_ = v___y_2018_;
goto v___jp_2000_;
}
else
{
v___y_2001_ = v___y_2013_;
v___y_2002_ = v___y_2014_;
v___y_2003_ = v___y_2015_;
v___y_2004_ = v___y_2016_;
v___y_2005_ = v___y_2017_;
v___y_2006_ = v___x_2020_;
goto v___jp_2000_;
}
}
v___jp_2022_:
{
uint8_t v___x_2028_; uint32_t v___x_2029_; uint8_t v___x_2030_; uint32_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2028_ = l_Lean_Expr_Data_approxDepth(v___y_2026_);
v___x_2029_ = lean_uint8_to_uint32(v___x_2028_);
v___x_2030_ = l_Lean_Expr_Data_approxDepth(v___y_2025_);
v___x_2031_ = lean_uint8_to_uint32(v___x_2030_);
v___x_2032_ = lean_uint32_dec_le(v___x_2029_, v___x_2031_);
if (v___x_2032_ == 0)
{
v___y_2013_ = v___y_2023_;
v___y_2014_ = v___y_2024_;
v___y_2015_ = v___y_2025_;
v___y_2016_ = v___y_2026_;
v___y_2017_ = v___y_2027_;
v___y_2018_ = v___x_2029_;
goto v___jp_2012_;
}
else
{
v___y_2013_ = v___y_2023_;
v___y_2014_ = v___y_2024_;
v___y_2015_ = v___y_2025_;
v___y_2016_ = v___y_2026_;
v___y_2017_ = v___y_2027_;
v___y_2018_ = v___x_2031_;
goto v___jp_2012_;
}
}
v___jp_2033_:
{
uint32_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2039_ = l_Lean_Expr_Data_looseBVarRange(v___y_2034_);
v___x_2040_ = lean_uint32_to_nat(v___x_2039_);
v___x_2041_ = lean_unsigned_to_nat(1u);
v___x_2042_ = lean_nat_sub(v___x_2040_, v___x_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_nat_dec_le(v___y_2038_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_dec(v___x_2042_);
v___y_2023_ = v___y_2034_;
v___y_2024_ = v___y_2035_;
v___y_2025_ = v___y_2036_;
v___y_2026_ = v___y_2037_;
v___y_2027_ = v___y_2038_;
goto v___jp_2022_;
}
else
{
lean_dec(v___y_2038_);
v___y_2023_ = v___y_2034_;
v___y_2024_ = v___y_2035_;
v___y_2025_ = v___y_2036_;
v___y_2026_ = v___y_2037_;
v___y_2027_ = v___x_2042_;
goto v___jp_2022_;
}
}
v___jp_2044_:
{
uint64_t v___x_2046_; uint32_t v___x_2047_; uint32_t v___x_2048_; uint64_t v___x_2049_; uint32_t v___x_2050_; uint32_t v___x_2051_; uint64_t v___x_2052_; uint32_t v___x_2053_; uint32_t v___x_2054_; uint32_t v___x_2055_; lean_object* v___x_2056_; uint32_t v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2046_ = lean_expr_data(v_type_1949_);
v___x_2047_ = lean_uint64_to_uint32(v___x_2046_);
v___x_2048_ = lean_uint32_mix_hash(v___y_2045_, v___x_2047_);
v___x_2049_ = lean_expr_data(v_value_1950_);
v___x_2050_ = lean_uint64_to_uint32(v___x_2049_);
v___x_2051_ = lean_uint32_mix_hash(v___x_2048_, v___x_2050_);
v___x_2052_ = lean_expr_data(v_body_1951_);
v___x_2053_ = lean_uint64_to_uint32(v___x_2052_);
v___x_2054_ = lean_uint32_mix_hash(v___x_2051_, v___x_2053_);
v___x_2055_ = l_Lean_Expr_Data_looseBVarRange(v___x_2046_);
v___x_2056_ = lean_uint32_to_nat(v___x_2055_);
v___x_2057_ = l_Lean_Expr_Data_looseBVarRange(v___x_2049_);
v___x_2058_ = lean_uint32_to_nat(v___x_2057_);
v___x_2059_ = lean_nat_dec_le(v___x_2056_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_dec(v___x_2058_);
v___y_2034_ = v___x_2052_;
v___y_2035_ = v___x_2054_;
v___y_2036_ = v___x_2049_;
v___y_2037_ = v___x_2046_;
v___y_2038_ = v___x_2056_;
goto v___jp_2033_;
}
else
{
lean_dec(v___x_2056_);
v___y_2034_ = v___x_2052_;
v___y_2035_ = v___x_2054_;
v___y_2036_ = v___x_2049_;
v___y_2037_ = v___x_2046_;
v___y_2038_ = v___x_2058_;
goto v___jp_2033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2062_, lean_object* v_type_2063_, lean_object* v_value_2064_, lean_object* v_body_2065_, lean_object* v_nondep_2066_){
_start:
{
uint8_t v_nondep_boxed_2067_; lean_object* v_res_2068_; 
v_nondep_boxed_2067_ = lean_unbox(v_nondep_2066_);
v_res_2068_ = l_Lean_Expr_letE___override(v_declName_2062_, v_type_2063_, v_value_2064_, v_body_2065_, v_nondep_boxed_2067_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2069_){
_start:
{
uint64_t v___x_2070_; uint64_t v___x_2071_; uint64_t v___x_2072_; uint32_t v___x_2073_; lean_object* v___x_2074_; uint32_t v___x_2075_; uint8_t v___x_2076_; uint64_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2070_ = 3ULL;
v___x_2071_ = l_Lean_Literal_hash(v_a_2069_);
v___x_2072_ = lean_uint64_mix_hash(v___x_2070_, v___x_2071_);
v___x_2073_ = lean_uint64_to_uint32(v___x_2072_);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = 0;
v___x_2076_ = 0;
v___x_2077_ = lean_expr_mk_data(v___x_2073_, v___x_2074_, v___x_2075_, v___x_2076_, v___x_2076_, v___x_2076_, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2078_, 0, v_a_2069_);
lean_ctor_set_uint64(v___x_2078_, sizeof(void*)*1, v___x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2079_, lean_object* v_expr_2080_){
_start:
{
uint32_t v___x_2081_; uint64_t v___x_2082_; uint32_t v___x_2083_; uint32_t v___x_2084_; uint32_t v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; uint32_t v___x_2088_; uint32_t v___x_2089_; uint32_t v___x_2090_; uint8_t v___x_2091_; uint8_t v___x_2092_; uint8_t v___x_2093_; uint8_t v___x_2094_; uint64_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2081_ = 19;
v___x_2082_ = lean_expr_data(v_expr_2080_);
v___x_2083_ = lean_uint64_to_uint32(v___x_2082_);
v___x_2084_ = lean_uint32_mix_hash(v___x_2081_, v___x_2083_);
v___x_2085_ = l_Lean_Expr_Data_looseBVarRange(v___x_2082_);
v___x_2086_ = lean_uint32_to_nat(v___x_2085_);
v___x_2087_ = l_Lean_Expr_Data_approxDepth(v___x_2082_);
v___x_2088_ = lean_uint8_to_uint32(v___x_2087_);
v___x_2089_ = 1;
v___x_2090_ = lean_uint32_add(v___x_2088_, v___x_2089_);
v___x_2091_ = l_Lean_Expr_Data_hasFVar(v___x_2082_);
v___x_2092_ = l_Lean_Expr_Data_hasExprMVar(v___x_2082_);
v___x_2093_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2082_);
v___x_2094_ = l_Lean_Expr_Data_hasLevelParam(v___x_2082_);
v___x_2095_ = lean_expr_mk_data(v___x_2084_, v___x_2086_, v___x_2090_, v___x_2091_, v___x_2092_, v___x_2093_, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2096_, 0, v_data_2079_);
lean_ctor_set(v___x_2096_, 1, v_expr_2080_);
lean_ctor_set_uint64(v___x_2096_, sizeof(void*)*2, v___x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2097_, lean_object* v_idx_2098_, lean_object* v_struct_2099_){
_start:
{
uint64_t v___x_2100_; uint64_t v___y_2102_; 
v___x_2100_ = 23ULL;
if (lean_obj_tag(v_typeName_2097_) == 0)
{
uint64_t v___x_2122_; 
v___x_2122_ = 1723ULL;
v___y_2102_ = v___x_2122_;
goto v___jp_2101_;
}
else
{
uint64_t v_hash_2123_; 
v_hash_2123_ = lean_ctor_get_uint64(v_typeName_2097_, sizeof(void*)*2);
v___y_2102_ = v_hash_2123_;
goto v___jp_2101_;
}
v___jp_2101_:
{
uint64_t v___x_2103_; uint64_t v___x_2104_; uint64_t v___x_2105_; uint32_t v___x_2106_; uint64_t v___x_2107_; uint32_t v___x_2108_; uint32_t v___x_2109_; uint32_t v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; uint32_t v___x_2113_; uint32_t v___x_2114_; uint32_t v___x_2115_; uint8_t v___x_2116_; uint8_t v___x_2117_; uint8_t v___x_2118_; uint8_t v___x_2119_; uint64_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2103_ = lean_uint64_of_nat(v_idx_2098_);
v___x_2104_ = lean_uint64_mix_hash(v___y_2102_, v___x_2103_);
v___x_2105_ = lean_uint64_mix_hash(v___x_2100_, v___x_2104_);
v___x_2106_ = lean_uint64_to_uint32(v___x_2105_);
v___x_2107_ = lean_expr_data(v_struct_2099_);
v___x_2108_ = lean_uint64_to_uint32(v___x_2107_);
v___x_2109_ = lean_uint32_mix_hash(v___x_2106_, v___x_2108_);
v___x_2110_ = l_Lean_Expr_Data_looseBVarRange(v___x_2107_);
v___x_2111_ = lean_uint32_to_nat(v___x_2110_);
v___x_2112_ = l_Lean_Expr_Data_approxDepth(v___x_2107_);
v___x_2113_ = lean_uint8_to_uint32(v___x_2112_);
v___x_2114_ = 1;
v___x_2115_ = lean_uint32_add(v___x_2113_, v___x_2114_);
v___x_2116_ = l_Lean_Expr_Data_hasFVar(v___x_2107_);
v___x_2117_ = l_Lean_Expr_Data_hasExprMVar(v___x_2107_);
v___x_2118_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2107_);
v___x_2119_ = l_Lean_Expr_Data_hasLevelParam(v___x_2107_);
v___x_2120_ = lean_expr_mk_data(v___x_2109_, v___x_2111_, v___x_2115_, v___x_2116_, v___x_2117_, v___x_2118_, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2121_, 0, v_typeName_2097_);
lean_ctor_set(v___x_2121_, 1, v_idx_2098_);
lean_ctor_set(v___x_2121_, 2, v_struct_2099_);
lean_ctor_set_uint64(v___x_2121_, sizeof(void*)*3, v___x_2120_);
return v___x_2121_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2124_){
_start:
{
if (lean_obj_tag(v_x_2124_) == 0)
{
uint8_t v___x_2125_; 
v___x_2125_ = 0;
return v___x_2125_;
}
else
{
lean_object* v_head_2126_; lean_object* v_tail_2127_; uint8_t v___x_2128_; 
v_head_2126_ = lean_ctor_get(v_x_2124_, 0);
v_tail_2127_ = lean_ctor_get(v_x_2124_, 1);
v___x_2128_ = l_Lean_Level_hasMVar(v_head_2126_);
if (v___x_2128_ == 0)
{
v_x_2124_ = v_tail_2127_;
goto _start;
}
else
{
return v___x_2128_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2130_){
_start:
{
uint8_t v_res_2131_; lean_object* v_r_2132_; 
v_res_2131_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2130_);
lean_dec(v_x_2130_);
v_r_2132_ = lean_box(v_res_2131_);
return v_r_2132_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2133_){
_start:
{
if (lean_obj_tag(v_x_2133_) == 0)
{
uint8_t v___x_2134_; 
v___x_2134_ = 0;
return v___x_2134_;
}
else
{
lean_object* v_head_2135_; lean_object* v_tail_2136_; uint8_t v___x_2137_; 
v_head_2135_ = lean_ctor_get(v_x_2133_, 0);
v_tail_2136_ = lean_ctor_get(v_x_2133_, 1);
v___x_2137_ = l_Lean_Level_hasParam(v_head_2135_);
if (v___x_2137_ == 0)
{
v_x_2133_ = v_tail_2136_;
goto _start;
}
else
{
return v___x_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2139_){
_start:
{
uint8_t v_res_2140_; lean_object* v_r_2141_; 
v_res_2140_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2139_);
lean_dec(v_x_2139_);
v_r_2141_ = lean_box(v_res_2140_);
return v_r_2141_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2142_, lean_object* v_x_2143_){
_start:
{
if (lean_obj_tag(v_x_2143_) == 0)
{
return v_x_2142_;
}
else
{
lean_object* v_head_2144_; lean_object* v_tail_2145_; uint64_t v___x_2146_; uint64_t v___x_2147_; 
v_head_2144_ = lean_ctor_get(v_x_2143_, 0);
v_tail_2145_ = lean_ctor_get(v_x_2143_, 1);
v___x_2146_ = l_Lean_Level_hash(v_head_2144_);
v___x_2147_ = lean_uint64_mix_hash(v_x_2142_, v___x_2146_);
v_x_2142_ = v___x_2147_;
v_x_2143_ = v_tail_2145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2149_, lean_object* v_x_2150_){
_start:
{
uint64_t v_x_1721__boxed_2151_; uint64_t v_res_2152_; lean_object* v_r_2153_; 
v_x_1721__boxed_2151_ = lean_unbox_uint64(v_x_2149_);
lean_dec_ref(v_x_2149_);
v_res_2152_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1721__boxed_2151_, v_x_2150_);
lean_dec(v_x_2150_);
v_r_2153_ = lean_box_uint64(v_res_2152_);
return v_r_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2154_, lean_object* v_us_2155_){
_start:
{
uint64_t v___x_2156_; uint64_t v___y_2158_; 
v___x_2156_ = 5ULL;
if (lean_obj_tag(v_declName_2154_) == 0)
{
uint64_t v___x_2171_; 
v___x_2171_ = 1723ULL;
v___y_2158_ = v___x_2171_;
goto v___jp_2157_;
}
else
{
uint64_t v_hash_2172_; 
v_hash_2172_ = lean_ctor_get_uint64(v_declName_2154_, sizeof(void*)*2);
v___y_2158_ = v_hash_2172_;
goto v___jp_2157_;
}
v___jp_2157_:
{
uint64_t v___x_2159_; uint64_t v___x_2160_; uint64_t v___x_2161_; uint64_t v___x_2162_; uint32_t v___x_2163_; lean_object* v___x_2164_; uint32_t v___x_2165_; uint8_t v___x_2166_; uint8_t v___x_2167_; uint8_t v___x_2168_; uint64_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2159_ = 7ULL;
v___x_2160_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2159_, v_us_2155_);
v___x_2161_ = lean_uint64_mix_hash(v___y_2158_, v___x_2160_);
v___x_2162_ = lean_uint64_mix_hash(v___x_2156_, v___x_2161_);
v___x_2163_ = lean_uint64_to_uint32(v___x_2162_);
v___x_2164_ = lean_unsigned_to_nat(0u);
v___x_2165_ = 0;
v___x_2166_ = 0;
v___x_2167_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2155_);
v___x_2168_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2155_);
v___x_2169_ = lean_expr_mk_data(v___x_2163_, v___x_2164_, v___x_2165_, v___x_2166_, v___x_2166_, v___x_2167_, v___x_2168_);
v___x_2170_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2170_, 0, v_declName_2154_);
lean_ctor_set(v___x_2170_, 1, v_us_2155_);
lean_ctor_set_uint64(v___x_2170_, sizeof(void*)*2, v___x_2169_);
return v___x_2170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = l_Lean_instReprLevel_repr(v___y_2173_, v___x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_){
_start:
{
if (lean_obj_tag(v_x_2178_) == 0)
{
lean_dec(v_x_2176_);
return v_x_2177_;
}
else
{
lean_object* v_head_2179_; lean_object* v_tail_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2191_; 
v_head_2179_ = lean_ctor_get(v_x_2178_, 0);
v_tail_2180_ = lean_ctor_get(v_x_2178_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_x_2178_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2182_ = v_x_2178_;
v_isShared_2183_ = v_isSharedCheck_2191_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_tail_2180_);
lean_inc(v_head_2179_);
lean_dec(v_x_2178_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2191_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
lean_inc(v_x_2176_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 5);
lean_ctor_set(v___x_2182_, 1, v_x_2176_);
lean_ctor_set(v___x_2182_, 0, v_x_2177_);
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_x_2177_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_x_2176_);
v___x_2185_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = l_Lean_instReprLevel_repr(v_head_2179_, v___x_2186_);
v___x_2188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2185_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v_x_2177_ = v___x_2188_;
v_x_2178_ = v_tail_2180_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 0)
{
lean_dec(v_x_2192_);
return v_x_2193_;
}
else
{
lean_object* v_head_2195_; lean_object* v_tail_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2207_; 
v_head_2195_ = lean_ctor_get(v_x_2194_, 0);
v_tail_2196_ = lean_ctor_get(v_x_2194_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_x_2194_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2198_ = v_x_2194_;
v_isShared_2199_ = v_isSharedCheck_2207_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_tail_2196_);
lean_inc(v_head_2195_);
lean_dec(v_x_2194_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2207_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
lean_inc(v_x_2192_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set_tag(v___x_2198_, 5);
lean_ctor_set(v___x_2198_, 1, v_x_2192_);
lean_ctor_set(v___x_2198_, 0, v_x_2193_);
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_x_2193_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_x_2192_);
v___x_2201_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = l_Lean_instReprLevel_repr(v_head_2195_, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2201_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2192_, v___x_2204_, v_tail_2196_);
return v___x_2205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
if (lean_obj_tag(v_x_2208_) == 0)
{
lean_object* v___x_2210_; 
lean_dec(v_x_2209_);
v___x_2210_ = lean_box(0);
return v___x_2210_;
}
else
{
lean_object* v_tail_2211_; 
v_tail_2211_ = lean_ctor_get(v_x_2208_, 1);
if (lean_obj_tag(v_tail_2211_) == 0)
{
lean_object* v_head_2212_; lean_object* v___x_2213_; 
lean_dec(v_x_2209_);
v_head_2212_ = lean_ctor_get(v_x_2208_, 0);
lean_inc(v_head_2212_);
lean_dec_ref_known(v_x_2208_, 2);
v___x_2213_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2212_);
return v___x_2213_;
}
else
{
lean_object* v_head_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_inc(v_tail_2211_);
v_head_2214_ = lean_ctor_get(v_x_2208_, 0);
lean_inc(v_head_2214_);
lean_dec_ref_known(v_x_2208_, 2);
v___x_2215_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2214_);
v___x_2216_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2209_, v___x_2215_, v_tail_2211_);
return v___x_2216_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2229_ = lean_string_length(v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2231_ = lean_nat_to_int(v___x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2236_){
_start:
{
if (lean_obj_tag(v_a_2236_) == 0)
{
lean_object* v___x_2237_; 
v___x_2237_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2237_;
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; 
v___x_2238_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2239_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2236_, v___x_2238_);
v___x_2240_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2241_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v___x_2239_);
v___x_2243_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2240_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = 0;
v___x_2247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2247_, 0, v___x_2245_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*1, v___x_2246_);
return v___x_2247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2320_, lean_object* v_prec_2321_){
_start:
{
switch(lean_obj_tag(v_x_2320_))
{
case 0:
{
lean_object* v_deBruijnIndex_2322_; lean_object* v___y_2324_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_deBruijnIndex_2322_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_deBruijnIndex_2322_);
lean_dec_ref_known(v_x_2320_, 1);
v___x_2333_ = lean_unsigned_to_nat(1024u);
v___x_2334_ = lean_nat_dec_le(v___x_2333_, v_prec_2321_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; 
v___x_2335_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2324_ = v___x_2335_;
goto v___jp_2323_;
}
else
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2324_ = v___x_2336_;
goto v___jp_2323_;
}
v___jp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2325_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2326_ = l_Nat_reprFast(v_deBruijnIndex_2322_);
v___x_2327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
v___x_2328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2325_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
lean_inc(v___y_2324_);
v___x_2329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___y_2324_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = 0;
v___x_2331_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*1, v___x_2330_);
v___x_2332_ = l_Repr_addAppParen(v___x_2331_, v_prec_2321_);
return v___x_2332_;
}
}
case 1:
{
lean_object* v_fvarId_2337_; lean_object* v___y_2339_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_fvarId_2337_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_fvarId_2337_);
lean_dec_ref_known(v_x_2320_, 1);
v___x_2348_ = lean_unsigned_to_nat(1024u);
v___x_2349_ = lean_nat_dec_le(v___x_2348_, v_prec_2321_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2339_ = v___x_2350_;
goto v___jp_2338_;
}
else
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2339_ = v___x_2351_;
goto v___jp_2338_;
}
v___jp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2340_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2341_ = lean_unsigned_to_nat(1024u);
v___x_2342_ = l_Lean_Name_reprPrec(v_fvarId_2337_, v___x_2341_);
v___x_2343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2340_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
lean_inc(v___y_2339_);
v___x_2344_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___y_2339_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = 0;
v___x_2346_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*1, v___x_2345_);
v___x_2347_ = l_Repr_addAppParen(v___x_2346_, v_prec_2321_);
return v___x_2347_;
}
}
case 2:
{
lean_object* v_mvarId_2352_; lean_object* v___y_2354_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_mvarId_2352_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_mvarId_2352_);
lean_dec_ref_known(v_x_2320_, 1);
v___x_2363_ = lean_unsigned_to_nat(1024u);
v___x_2364_ = lean_nat_dec_le(v___x_2363_, v_prec_2321_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2354_ = v___x_2365_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2354_ = v___x_2366_;
goto v___jp_2353_;
}
v___jp_2353_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2355_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2356_ = lean_unsigned_to_nat(1024u);
v___x_2357_ = l_Lean_Name_reprPrec(v_mvarId_2352_, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2355_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
lean_inc(v___y_2354_);
v___x_2359_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___y_2354_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = 0;
v___x_2361_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*1, v___x_2360_);
v___x_2362_ = l_Repr_addAppParen(v___x_2361_, v_prec_2321_);
return v___x_2362_;
}
}
case 3:
{
lean_object* v_u_2367_; lean_object* v___y_2369_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
v_u_2367_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_u_2367_);
lean_dec_ref_known(v_x_2320_, 1);
v___x_2378_ = lean_unsigned_to_nat(1024u);
v___x_2379_ = lean_nat_dec_le(v___x_2378_, v_prec_2321_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2369_ = v___x_2380_;
goto v___jp_2368_;
}
else
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2369_ = v___x_2381_;
goto v___jp_2368_;
}
v___jp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2370_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2371_ = lean_unsigned_to_nat(1024u);
v___x_2372_ = l_Lean_instReprLevel_repr(v_u_2367_, v___x_2371_);
v___x_2373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2370_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
lean_inc(v___y_2369_);
v___x_2374_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___y_2369_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = 0;
v___x_2376_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set_uint8(v___x_2376_, sizeof(void*)*1, v___x_2375_);
v___x_2377_ = l_Repr_addAppParen(v___x_2376_, v_prec_2321_);
return v___x_2377_;
}
}
case 4:
{
lean_object* v_declName_2382_; lean_object* v_us_2383_; lean_object* v___y_2385_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_declName_2382_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_declName_2382_);
v_us_2383_ = lean_ctor_get(v_x_2320_, 1);
lean_inc(v_us_2383_);
lean_dec_ref_known(v_x_2320_, 2);
v___x_2398_ = lean_unsigned_to_nat(1024u);
v___x_2399_ = lean_nat_dec_le(v___x_2398_, v_prec_2321_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2385_ = v___x_2400_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2385_ = v___x_2401_;
goto v___jp_2384_;
}
v___jp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2386_ = lean_box(1);
v___x_2387_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2388_ = lean_unsigned_to_nat(1024u);
v___x_2389_ = l_Lean_Name_reprPrec(v_declName_2382_, v___x_2388_);
v___x_2390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2387_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v___x_2386_);
v___x_2392_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2383_);
v___x_2393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
lean_inc(v___y_2385_);
v___x_2394_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___y_2385_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = 0;
v___x_2396_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*1, v___x_2395_);
v___x_2397_ = l_Repr_addAppParen(v___x_2396_, v_prec_2321_);
return v___x_2397_;
}
}
case 5:
{
lean_object* v_fn_2402_; lean_object* v_arg_2403_; lean_object* v___x_2404_; lean_object* v___y_2406_; uint8_t v___x_2418_; 
v_fn_2402_ = lean_ctor_get(v_x_2320_, 0);
lean_inc_ref(v_fn_2402_);
v_arg_2403_ = lean_ctor_get(v_x_2320_, 1);
lean_inc_ref(v_arg_2403_);
lean_dec_ref_known(v_x_2320_, 2);
v___x_2404_ = lean_unsigned_to_nat(1024u);
v___x_2418_ = lean_nat_dec_le(v___x_2404_, v_prec_2321_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2406_ = v___x_2419_;
goto v___jp_2405_;
}
else
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2406_ = v___x_2420_;
goto v___jp_2405_;
}
v___jp_2405_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2407_ = lean_box(1);
v___x_2408_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2409_ = l_Lean_instReprExpr_repr(v_fn_2402_, v___x_2404_);
v___x_2410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___x_2407_);
v___x_2412_ = l_Lean_instReprExpr_repr(v_arg_2403_, v___x_2404_);
v___x_2413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
lean_inc(v___y_2406_);
v___x_2414_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___y_2406_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = 0;
v___x_2416_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*1, v___x_2415_);
v___x_2417_ = l_Repr_addAppParen(v___x_2416_, v_prec_2321_);
return v___x_2417_;
}
}
case 6:
{
lean_object* v_binderName_2421_; lean_object* v_binderType_2422_; lean_object* v_body_2423_; uint8_t v_binderInfo_2424_; lean_object* v___x_2425_; lean_object* v___y_2427_; uint8_t v___x_2445_; 
v_binderName_2421_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_binderName_2421_);
v_binderType_2422_ = lean_ctor_get(v_x_2320_, 1);
lean_inc_ref(v_binderType_2422_);
v_body_2423_ = lean_ctor_get(v_x_2320_, 2);
lean_inc_ref(v_body_2423_);
v_binderInfo_2424_ = lean_ctor_get_uint8(v_x_2320_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2320_, 3);
v___x_2425_ = lean_unsigned_to_nat(1024u);
v___x_2445_ = lean_nat_dec_le(v___x_2425_, v_prec_2321_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2427_ = v___x_2446_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2427_ = v___x_2447_;
goto v___jp_2426_;
}
v___jp_2426_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2428_ = lean_box(1);
v___x_2429_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2430_ = l_Lean_Name_reprPrec(v_binderName_2421_, v___x_2425_);
v___x_2431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
lean_ctor_set(v___x_2432_, 1, v___x_2428_);
v___x_2433_ = l_Lean_instReprExpr_repr(v_binderType_2422_, v___x_2425_);
v___x_2434_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v___x_2428_);
v___x_2436_ = l_Lean_instReprExpr_repr(v_body_2423_, v___x_2425_);
v___x_2437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v___x_2428_);
v___x_2439_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2424_, v___x_2425_);
v___x_2440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
lean_inc(v___y_2427_);
v___x_2441_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___y_2427_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = 0;
v___x_2443_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set_uint8(v___x_2443_, sizeof(void*)*1, v___x_2442_);
v___x_2444_ = l_Repr_addAppParen(v___x_2443_, v_prec_2321_);
return v___x_2444_;
}
}
case 7:
{
lean_object* v_binderName_2448_; lean_object* v_binderType_2449_; lean_object* v_body_2450_; uint8_t v_binderInfo_2451_; lean_object* v___x_2452_; lean_object* v___y_2454_; uint8_t v___x_2472_; 
v_binderName_2448_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_binderName_2448_);
v_binderType_2449_ = lean_ctor_get(v_x_2320_, 1);
lean_inc_ref(v_binderType_2449_);
v_body_2450_ = lean_ctor_get(v_x_2320_, 2);
lean_inc_ref(v_body_2450_);
v_binderInfo_2451_ = lean_ctor_get_uint8(v_x_2320_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2320_, 3);
v___x_2452_ = lean_unsigned_to_nat(1024u);
v___x_2472_ = lean_nat_dec_le(v___x_2452_, v_prec_2321_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2454_ = v___x_2473_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2454_ = v___x_2474_;
goto v___jp_2453_;
}
v___jp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2455_ = lean_box(1);
v___x_2456_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2457_ = l_Lean_Name_reprPrec(v_binderName_2448_, v___x_2452_);
v___x_2458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
lean_ctor_set(v___x_2459_, 1, v___x_2455_);
v___x_2460_ = l_Lean_instReprExpr_repr(v_binderType_2449_, v___x_2452_);
v___x_2461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v___x_2455_);
v___x_2463_ = l_Lean_instReprExpr_repr(v_body_2450_, v___x_2452_);
v___x_2464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2462_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
lean_ctor_set(v___x_2465_, 1, v___x_2455_);
v___x_2466_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2451_, v___x_2452_);
v___x_2467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
lean_inc(v___y_2454_);
v___x_2468_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___y_2454_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = 0;
v___x_2470_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*1, v___x_2469_);
v___x_2471_ = l_Repr_addAppParen(v___x_2470_, v_prec_2321_);
return v___x_2471_;
}
}
case 8:
{
lean_object* v_declName_2475_; lean_object* v_type_2476_; lean_object* v_value_2477_; lean_object* v_body_2478_; uint8_t v_nondep_2479_; lean_object* v___x_2480_; lean_object* v___y_2482_; uint8_t v___x_2503_; 
v_declName_2475_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_declName_2475_);
v_type_2476_ = lean_ctor_get(v_x_2320_, 1);
lean_inc_ref(v_type_2476_);
v_value_2477_ = lean_ctor_get(v_x_2320_, 2);
lean_inc_ref(v_value_2477_);
v_body_2478_ = lean_ctor_get(v_x_2320_, 3);
lean_inc_ref(v_body_2478_);
v_nondep_2479_ = lean_ctor_get_uint8(v_x_2320_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_2320_, 4);
v___x_2480_ = lean_unsigned_to_nat(1024u);
v___x_2503_ = lean_nat_dec_le(v___x_2480_, v_prec_2321_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2482_ = v___x_2504_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2482_ = v___x_2505_;
goto v___jp_2481_;
}
v___jp_2481_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2483_ = lean_box(1);
v___x_2484_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2485_ = l_Lean_Name_reprPrec(v_declName_2475_, v___x_2480_);
v___x_2486_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v___x_2483_);
v___x_2488_ = l_Lean_instReprExpr_repr(v_type_2476_, v___x_2480_);
v___x_2489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set(v___x_2490_, 1, v___x_2483_);
v___x_2491_ = l_Lean_instReprExpr_repr(v_value_2477_, v___x_2480_);
v___x_2492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
lean_ctor_set(v___x_2493_, 1, v___x_2483_);
v___x_2494_ = l_Lean_instReprExpr_repr(v_body_2478_, v___x_2480_);
v___x_2495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
lean_ctor_set(v___x_2496_, 1, v___x_2483_);
v___x_2497_ = l_Bool_repr___redArg(v_nondep_2479_);
v___x_2498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
lean_inc(v___y_2482_);
v___x_2499_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___y_2482_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = 0;
v___x_2501_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set_uint8(v___x_2501_, sizeof(void*)*1, v___x_2500_);
v___x_2502_ = l_Repr_addAppParen(v___x_2501_, v_prec_2321_);
return v___x_2502_;
}
}
case 9:
{
lean_object* v_a_2506_; lean_object* v___y_2508_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v_a_2506_ = lean_ctor_get(v_x_2320_, 0);
lean_inc_ref(v_a_2506_);
lean_dec_ref_known(v_x_2320_, 1);
v___x_2517_ = lean_unsigned_to_nat(1024u);
v___x_2518_ = lean_nat_dec_le(v___x_2517_, v_prec_2321_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2508_ = v___x_2519_;
goto v___jp_2507_;
}
else
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2508_ = v___x_2520_;
goto v___jp_2507_;
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2509_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2510_ = lean_unsigned_to_nat(1024u);
v___x_2511_ = l_Lean_instReprLiteral_repr(v_a_2506_, v___x_2510_);
v___x_2512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2509_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
lean_inc(v___y_2508_);
v___x_2513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2508_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = 0;
v___x_2515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*1, v___x_2514_);
v___x_2516_ = l_Repr_addAppParen(v___x_2515_, v_prec_2321_);
return v___x_2516_;
}
}
case 10:
{
lean_object* v_data_2521_; lean_object* v_expr_2522_; lean_object* v___x_2523_; lean_object* v___y_2525_; uint8_t v___x_2537_; 
v_data_2521_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_data_2521_);
v_expr_2522_ = lean_ctor_get(v_x_2320_, 1);
lean_inc_ref(v_expr_2522_);
lean_dec_ref_known(v_x_2320_, 2);
v___x_2523_ = lean_unsigned_to_nat(1024u);
v___x_2537_ = lean_nat_dec_le(v___x_2523_, v_prec_2321_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2525_ = v___x_2538_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2525_ = v___x_2539_;
goto v___jp_2524_;
}
v___jp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2526_ = lean_box(1);
v___x_2527_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2528_ = l_Lean_instReprKVMap_repr___redArg(v_data_2521_);
v___x_2529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v___x_2526_);
v___x_2531_ = l_Lean_instReprExpr_repr(v_expr_2522_, v___x_2523_);
v___x_2532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
lean_inc(v___y_2525_);
v___x_2533_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___y_2525_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = 0;
v___x_2535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set_uint8(v___x_2535_, sizeof(void*)*1, v___x_2534_);
v___x_2536_ = l_Repr_addAppParen(v___x_2535_, v_prec_2321_);
return v___x_2536_;
}
}
default: 
{
lean_object* v_typeName_2540_; lean_object* v_idx_2541_; lean_object* v_struct_2542_; lean_object* v___x_2543_; lean_object* v___y_2545_; uint8_t v___x_2561_; 
v_typeName_2540_ = lean_ctor_get(v_x_2320_, 0);
lean_inc(v_typeName_2540_);
v_idx_2541_ = lean_ctor_get(v_x_2320_, 1);
lean_inc(v_idx_2541_);
v_struct_2542_ = lean_ctor_get(v_x_2320_, 2);
lean_inc_ref(v_struct_2542_);
lean_dec_ref_known(v_x_2320_, 3);
v___x_2543_ = lean_unsigned_to_nat(1024u);
v___x_2561_ = lean_nat_dec_le(v___x_2543_, v_prec_2321_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2545_ = v___x_2562_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2545_ = v___x_2563_;
goto v___jp_2544_;
}
v___jp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2546_ = lean_box(1);
v___x_2547_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2548_ = l_Lean_Name_reprPrec(v_typeName_2540_, v___x_2543_);
v___x_2549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___x_2546_);
v___x_2551_ = l_Nat_reprFast(v_idx_2541_);
v___x_2552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2550_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v___x_2546_);
v___x_2555_ = l_Lean_instReprExpr_repr(v_struct_2542_, v___x_2543_);
v___x_2556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
lean_inc(v___y_2545_);
v___x_2557_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___y_2545_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = 0;
v___x_2559_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set_uint8(v___x_2559_, sizeof(void*)*1, v___x_2558_);
v___x_2560_ = l_Repr_addAppParen(v___x_2559_, v_prec_2321_);
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2564_, lean_object* v_prec_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_instReprExpr_repr(v_x_2564_, v_prec_2565_);
lean_dec(v_prec_2565_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_nat_to_int(v_a_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2569_, lean_object* v_n_2570_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2569_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2572_, lean_object* v_n_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2572_, v_n_2573_);
lean_dec(v_n_2573_);
return v_res_2574_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = lean_box(0);
v___x_2581_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2582_ = l_Lean_Expr_const___override(v___x_2581_, v___x_2580_);
return v___x_2582_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2596_){
_start:
{
switch(lean_obj_tag(v_x_2596_))
{
case 0:
{
lean_object* v___x_2597_; 
v___x_2597_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2597_;
}
case 1:
{
lean_object* v___x_2598_; 
v___x_2598_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2598_;
}
case 2:
{
lean_object* v___x_2599_; 
v___x_2599_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2599_;
}
case 3:
{
lean_object* v___x_2600_; 
v___x_2600_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2600_;
}
case 4:
{
lean_object* v___x_2601_; 
v___x_2601_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2601_;
}
case 5:
{
lean_object* v___x_2602_; 
v___x_2602_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2602_;
}
case 6:
{
lean_object* v___x_2603_; 
v___x_2603_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2603_;
}
case 7:
{
lean_object* v___x_2604_; 
v___x_2604_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2604_;
}
case 8:
{
lean_object* v___x_2605_; 
v___x_2605_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2605_;
}
case 9:
{
lean_object* v___x_2606_; 
v___x_2606_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2606_;
}
case 10:
{
lean_object* v___x_2607_; 
v___x_2607_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2607_;
}
default: 
{
lean_object* v___x_2608_; 
v___x_2608_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_Expr_ctorName(v_x_2609_);
lean_dec_ref(v_x_2609_);
return v_res_2610_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2611_){
_start:
{
uint64_t v___x_2612_; uint32_t v___x_2613_; uint64_t v___x_2614_; 
v___x_2612_ = lean_expr_data(v_e_2611_);
v___x_2613_ = lean_uint64_to_uint32(v___x_2612_);
v___x_2614_ = lean_uint32_to_uint64(v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2615_){
_start:
{
uint64_t v_res_2616_; lean_object* v_r_2617_; 
v_res_2616_ = l_Lean_Expr_hash(v_e_2615_);
lean_dec_ref(v_e_2615_);
v_r_2617_ = lean_box_uint64(v_res_2616_);
return v_r_2617_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2620_){
_start:
{
uint64_t v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = lean_expr_data(v_e_2620_);
v___x_2622_ = l_Lean_Expr_Data_hasFVar(v___x_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2623_){
_start:
{
uint8_t v_res_2624_; lean_object* v_r_2625_; 
v_res_2624_ = l_Lean_Expr_hasFVar(v_e_2623_);
lean_dec_ref(v_e_2623_);
v_r_2625_ = lean_box(v_res_2624_);
return v_r_2625_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2626_){
_start:
{
uint64_t v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = lean_expr_data(v_e_2626_);
v___x_2628_ = l_Lean_Expr_Data_hasExprMVar(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2629_){
_start:
{
uint8_t v_res_2630_; lean_object* v_r_2631_; 
v_res_2630_ = l_Lean_Expr_hasExprMVar(v_e_2629_);
lean_dec_ref(v_e_2629_);
v_r_2631_ = lean_box(v_res_2630_);
return v_r_2631_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2632_){
_start:
{
uint64_t v___x_2633_; uint8_t v___x_2634_; 
v___x_2633_ = lean_expr_data(v_e_2632_);
v___x_2634_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2635_){
_start:
{
uint8_t v_res_2636_; lean_object* v_r_2637_; 
v_res_2636_ = l_Lean_Expr_hasLevelMVar(v_e_2635_);
lean_dec_ref(v_e_2635_);
v_r_2637_ = lean_box(v_res_2636_);
return v_r_2637_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2638_){
_start:
{
uint64_t v_d_2639_; uint8_t v___x_2640_; 
v_d_2639_ = lean_expr_data(v_e_2638_);
v___x_2640_ = l_Lean_Expr_Data_hasExprMVar(v_d_2639_);
if (v___x_2640_ == 0)
{
uint8_t v___x_2641_; 
v___x_2641_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2639_);
return v___x_2641_;
}
else
{
return v___x_2640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2642_){
_start:
{
uint8_t v_res_2643_; lean_object* v_r_2644_; 
v_res_2643_ = l_Lean_Expr_hasMVar(v_e_2642_);
lean_dec_ref(v_e_2642_);
v_r_2644_ = lean_box(v_res_2643_);
return v_r_2644_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2645_){
_start:
{
uint64_t v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = lean_expr_data(v_e_2645_);
v___x_2647_ = l_Lean_Expr_Data_hasLevelParam(v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2648_){
_start:
{
uint8_t v_res_2649_; lean_object* v_r_2650_; 
v_res_2649_ = l_Lean_Expr_hasLevelParam(v_e_2648_);
lean_dec_ref(v_e_2648_);
v_r_2650_ = lean_box(v_res_2649_);
return v_r_2650_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2651_){
_start:
{
uint64_t v___x_2652_; uint8_t v___x_2653_; uint32_t v___x_2654_; 
v___x_2652_ = lean_expr_data(v_e_2651_);
v___x_2653_ = l_Lean_Expr_Data_approxDepth(v___x_2652_);
v___x_2654_ = lean_uint8_to_uint32(v___x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2655_){
_start:
{
uint32_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l_Lean_Expr_approxDepth(v_e_2655_);
lean_dec_ref(v_e_2655_);
v_r_2657_ = lean_box_uint32(v_res_2656_);
return v_r_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2658_){
_start:
{
uint64_t v___x_2659_; uint32_t v___x_2660_; lean_object* v___x_2661_; 
v___x_2659_ = lean_expr_data(v_e_2658_);
v___x_2660_ = l_Lean_Expr_Data_looseBVarRange(v___x_2659_);
v___x_2661_ = lean_uint32_to_nat(v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_Expr_looseBVarRange(v_e_2662_);
lean_dec_ref(v_e_2662_);
return v_res_2663_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2664_){
_start:
{
switch(lean_obj_tag(v_e_2664_))
{
case 7:
{
uint8_t v_binderInfo_2665_; 
v_binderInfo_2665_ = lean_ctor_get_uint8(v_e_2664_, sizeof(void*)*3 + 8);
return v_binderInfo_2665_;
}
case 6:
{
uint8_t v_binderInfo_2666_; 
v_binderInfo_2666_ = lean_ctor_get_uint8(v_e_2664_, sizeof(void*)*3 + 8);
return v_binderInfo_2666_;
}
default: 
{
uint8_t v___x_2667_; 
v___x_2667_ = 0;
return v___x_2667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2668_){
_start:
{
uint8_t v_res_2669_; lean_object* v_r_2670_; 
v_res_2669_ = l_Lean_Expr_binderInfo(v_e_2668_);
lean_dec_ref(v_e_2668_);
v_r_2670_ = lean_box(v_res_2669_);
return v_r_2670_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2671_){
_start:
{
uint64_t v___x_2672_; 
v___x_2672_ = l_Lean_Expr_hash(v_a_2671_);
lean_dec_ref(v_a_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2673_){
_start:
{
uint64_t v_res_2674_; lean_object* v_r_2675_; 
v_res_2674_ = lean_expr_hash(v_a_2673_);
v_r_2675_ = lean_box_uint64(v_res_2674_);
return v_r_2675_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2676_){
_start:
{
uint8_t v___x_2677_; 
v___x_2677_ = l_Lean_Expr_hasFVar(v_e_2676_);
lean_dec_ref(v_e_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2678_){
_start:
{
uint8_t v_res_2679_; lean_object* v_r_2680_; 
v_res_2679_ = lean_expr_has_fvar(v_e_2678_);
v_r_2680_ = lean_box(v_res_2679_);
return v_r_2680_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2681_){
_start:
{
uint8_t v___x_2682_; 
v___x_2682_ = l_Lean_Expr_hasExprMVar(v_e_2681_);
lean_dec_ref(v_e_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2683_){
_start:
{
uint8_t v_res_2684_; lean_object* v_r_2685_; 
v_res_2684_ = lean_expr_has_expr_mvar(v_e_2683_);
v_r_2685_ = lean_box(v_res_2684_);
return v_r_2685_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2686_){
_start:
{
uint8_t v___x_2687_; 
v___x_2687_ = l_Lean_Expr_hasLevelMVar(v_e_2686_);
lean_dec_ref(v_e_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2688_){
_start:
{
uint8_t v_res_2689_; lean_object* v_r_2690_; 
v_res_2689_ = lean_expr_has_level_mvar(v_e_2688_);
v_r_2690_ = lean_box(v_res_2689_);
return v_r_2690_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2691_){
_start:
{
uint8_t v___x_2692_; 
v___x_2692_ = l_Lean_Expr_hasLevelParam(v_e_2691_);
lean_dec_ref(v_e_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2693_){
_start:
{
uint8_t v_res_2694_; lean_object* v_r_2695_; 
v_res_2694_ = lean_expr_has_level_param(v_e_2693_);
v_r_2695_ = lean_box(v_res_2694_);
return v_r_2695_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2696_){
_start:
{
uint64_t v___x_2697_; uint32_t v___x_2698_; 
v___x_2697_ = lean_expr_data(v_e_2696_);
lean_dec_ref(v_e_2696_);
v___x_2698_ = l_Lean_Expr_Data_looseBVarRange(v___x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2699_){
_start:
{
uint32_t v_res_2700_; lean_object* v_r_2701_; 
v_res_2700_ = lean_expr_loose_bvar_range(v_e_2699_);
v_r_2701_ = lean_box_uint32(v_res_2700_);
return v_r_2701_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2702_){
_start:
{
uint8_t v___x_2703_; 
v___x_2703_ = l_Lean_Expr_binderInfo(v_e_2702_);
lean_dec_ref(v_e_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2704_){
_start:
{
uint8_t v_res_2705_; lean_object* v_r_2706_; 
v_res_2705_ = lean_expr_binder_info(v_e_2704_);
v_r_2706_ = lean_box(v_res_2705_);
return v_r_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2707_, lean_object* v_us_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Expr_const___override(v_declName_2707_, v_us_2708_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = lean_box(0);
v___x_2714_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2715_ = l_Lean_Expr_const___override(v___x_2714_, v___x_2713_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = lean_box(0);
v___x_2720_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2721_ = l_Lean_Expr_const___override(v___x_2720_, v___x_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2722_){
_start:
{
if (lean_obj_tag(v_x_2722_) == 0)
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2723_;
}
else
{
lean_object* v___x_2724_; 
v___x_2724_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_Literal_type(v_x_2725_);
lean_dec_ref(v_x_2725_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2727_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Literal_type(v_a_2727_);
lean_dec_ref(v_a_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2729_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_Expr_bvar___override(v_idx_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2731_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Expr_sort___override(v_u_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_Expr_fvar___override(v_fvarId_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Expr_mvar___override(v_mvarId_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2737_, lean_object* v_e_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Expr_mdata___override(v_m_2737_, v_e_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2740_, lean_object* v_idx_2741_, lean_object* v_struct_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_Expr_proj___override(v_structName_2740_, v_idx_2741_, v_struct_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Expr_app___override(v_f_2744_, v_a_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2747_, uint8_t v_bi_2748_, lean_object* v_t_2749_, lean_object* v_b_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_Expr_lam___override(v_x_2747_, v_t_2749_, v_b_2750_, v_bi_2748_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2752_, lean_object* v_bi_2753_, lean_object* v_t_2754_, lean_object* v_b_2755_){
_start:
{
uint8_t v_bi_boxed_2756_; lean_object* v_res_2757_; 
v_bi_boxed_2756_ = lean_unbox(v_bi_2753_);
v_res_2757_ = l_Lean_mkLambda(v_x_2752_, v_bi_boxed_2756_, v_t_2754_, v_b_2755_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2758_, uint8_t v_bi_2759_, lean_object* v_t_2760_, lean_object* v_b_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_Expr_forallE___override(v_x_2758_, v_t_2760_, v_b_2761_, v_bi_2759_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2763_, lean_object* v_bi_2764_, lean_object* v_t_2765_, lean_object* v_b_2766_){
_start:
{
uint8_t v_bi_boxed_2767_; lean_object* v_res_2768_; 
v_bi_boxed_2767_ = lean_unbox(v_bi_2764_);
v_res_2768_ = l_Lean_mkForall(v_x_2763_, v_bi_boxed_2767_, v_t_2765_, v_b_2766_);
return v_res_2768_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2775_ = lean_box(0);
v___x_2776_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2777_ = l_Lean_Expr_const___override(v___x_2776_, v___x_2775_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2778_){
_start:
{
lean_object* v___x_2779_; uint8_t v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2779_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2780_ = 0;
v___x_2781_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2782_ = l_Lean_Expr_forallE___override(v___x_2779_, v___x_2781_, v_type_2778_, v___x_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2783_){
_start:
{
lean_object* v___x_2784_; uint8_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2784_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2785_ = 0;
v___x_2786_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2787_ = l_Lean_Expr_lam___override(v___x_2784_, v___x_2786_, v_type_2783_, v___x_2785_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2788_, lean_object* v_t_2789_, lean_object* v_v_2790_, lean_object* v_b_2791_, uint8_t v_nondep_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_Expr_letE___override(v_x_2788_, v_t_2789_, v_v_2790_, v_b_2791_, v_nondep_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2794_, lean_object* v_t_2795_, lean_object* v_v_2796_, lean_object* v_b_2797_, lean_object* v_nondep_2798_){
_start:
{
uint8_t v_nondep_boxed_2799_; lean_object* v_res_2800_; 
v_nondep_boxed_2799_ = lean_unbox(v_nondep_2798_);
v_res_2800_ = l_Lean_mkLet(v_x_2794_, v_t_2795_, v_v_2796_, v_b_2797_, v_nondep_boxed_2799_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2801_, lean_object* v_t_2802_, lean_object* v_v_2803_, lean_object* v_b_2804_){
_start:
{
uint8_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = 1;
v___x_2806_ = l_Lean_Expr_letE___override(v_x_2801_, v_t_2802_, v_v_2803_, v_b_2804_, v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2807_, lean_object* v_a_2808_, lean_object* v_b_2809_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = l_Lean_Expr_app___override(v_f_2807_, v_a_2808_);
v___x_2811_ = l_Lean_Expr_app___override(v___x_2810_, v_b_2809_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2812_, lean_object* v_a_2813_, lean_object* v_b_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_mkAppB(v_f_2812_, v_a_2813_, v_b_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2816_, lean_object* v_a_2817_, lean_object* v_b_2818_, lean_object* v_c_2819_){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = l_Lean_mkAppB(v_f_2816_, v_a_2817_, v_b_2818_);
v___x_2821_ = l_Lean_Expr_app___override(v___x_2820_, v_c_2819_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2822_, lean_object* v_a_2823_, lean_object* v_b_2824_, lean_object* v_c_2825_, lean_object* v_d_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = l_Lean_mkAppB(v_f_2822_, v_a_2823_, v_b_2824_);
v___x_2828_ = l_Lean_mkAppB(v___x_2827_, v_c_2825_, v_d_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2829_, lean_object* v_a_2830_, lean_object* v_b_2831_, lean_object* v_c_2832_, lean_object* v_d_2833_, lean_object* v_e_2834_){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = l_Lean_mkApp4(v_f_2829_, v_a_2830_, v_b_2831_, v_c_2832_, v_d_2833_);
v___x_2836_ = l_Lean_Expr_app___override(v___x_2835_, v_e_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2837_, lean_object* v_a_2838_, lean_object* v_b_2839_, lean_object* v_c_2840_, lean_object* v_d_2841_, lean_object* v_e_u2081_2842_, lean_object* v_e_u2082_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = l_Lean_mkApp4(v_f_2837_, v_a_2838_, v_b_2839_, v_c_2840_, v_d_2841_);
v___x_2845_ = l_Lean_mkAppB(v___x_2844_, v_e_u2081_2842_, v_e_u2082_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2846_, lean_object* v_a_2847_, lean_object* v_b_2848_, lean_object* v_c_2849_, lean_object* v_d_2850_, lean_object* v_e_u2081_2851_, lean_object* v_e_u2082_2852_, lean_object* v_e_u2083_2853_){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = l_Lean_mkApp4(v_f_2846_, v_a_2847_, v_b_2848_, v_c_2849_, v_d_2850_);
v___x_2855_ = l_Lean_mkApp3(v___x_2854_, v_e_u2081_2851_, v_e_u2082_2852_, v_e_u2083_2853_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2856_, lean_object* v_a_2857_, lean_object* v_b_2858_, lean_object* v_c_2859_, lean_object* v_d_2860_, lean_object* v_e_u2081_2861_, lean_object* v_e_u2082_2862_, lean_object* v_e_u2083_2863_, lean_object* v_e_u2084_2864_){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = l_Lean_mkApp4(v_f_2856_, v_a_2857_, v_b_2858_, v_c_2859_, v_d_2860_);
v___x_2866_ = l_Lean_mkApp4(v___x_2865_, v_e_u2081_2861_, v_e_u2082_2862_, v_e_u2083_2863_, v_e_u2084_2864_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2867_, lean_object* v_a_2868_, lean_object* v_b_2869_, lean_object* v_c_2870_, lean_object* v_d_2871_, lean_object* v_e_u2081_2872_, lean_object* v_e_u2082_2873_, lean_object* v_e_u2083_2874_, lean_object* v_e_u2084_2875_, lean_object* v_e_u2085_2876_){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = l_Lean_mkApp4(v_f_2867_, v_a_2868_, v_b_2869_, v_c_2870_, v_d_2871_);
v___x_2878_ = l_Lean_mkApp5(v___x_2877_, v_e_u2081_2872_, v_e_u2082_2873_, v_e_u2083_2874_, v_e_u2084_2875_, v_e_u2085_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2879_, lean_object* v_a_2880_, lean_object* v_b_2881_, lean_object* v_c_2882_, lean_object* v_d_2883_, lean_object* v_e_u2081_2884_, lean_object* v_e_u2082_2885_, lean_object* v_e_u2083_2886_, lean_object* v_e_u2084_2887_, lean_object* v_e_u2085_2888_, lean_object* v_e_u2086_2889_){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = l_Lean_mkApp4(v_f_2879_, v_a_2880_, v_b_2881_, v_c_2882_, v_d_2883_);
v___x_2891_ = l_Lean_mkApp6(v___x_2890_, v_e_u2081_2884_, v_e_u2082_2885_, v_e_u2083_2886_, v_e_u2084_2887_, v_e_u2085_2888_, v_e_u2086_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_Expr_lit___override(v_l_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2894_){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_n_2894_);
v___x_2896_ = l_Lean_Expr_lit___override(v___x_2895_);
return v___x_2896_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = lean_box(0);
v___x_2901_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2902_ = l_Lean_Expr_const___override(v___x_2901_, v___x_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2903_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2905_ = l_Lean_Expr_app___override(v___x_2904_, v_n_2903_);
return v___x_2905_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2914_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2915_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2916_ = l_Lean_Expr_const___override(v___x_2915_, v___x_2914_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2917_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2918_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2919_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2917_);
v___x_2920_ = l_Lean_mkInstOfNatNat(v_n_2917_);
v___x_2921_ = l_Lean_mkApp3(v___x_2918_, v___x_2919_, v_n_2917_, v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2922_){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = l_Lean_mkRawNatLit(v_n_2922_);
v___x_2924_ = l_Lean_mkNatLitCore(v___x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2925_){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_s_2925_);
v___x_2927_ = l_Lean_Expr_lit___override(v___x_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_Expr_bvar___override(v_idx_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_Expr_fvar___override(v_fvarId_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_Expr_sort___override(v_u_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2934_, lean_object* v_lvls_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_Expr_const___override(v_c_2934_, v_lvls_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Expr_app___override(v_f_2937_, v_a_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2940_, lean_object* v_d_2941_, lean_object* v_b_2942_, uint8_t v_bi_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Expr_lam___override(v_n_2940_, v_d_2941_, v_b_2942_, v_bi_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2945_, lean_object* v_d_2946_, lean_object* v_b_2947_, lean_object* v_bi_2948_){
_start:
{
uint8_t v_bi_boxed_2949_; lean_object* v_res_2950_; 
v_bi_boxed_2949_ = lean_unbox(v_bi_2948_);
v_res_2950_ = lean_expr_mk_lambda(v_n_2945_, v_d_2946_, v_b_2947_, v_bi_boxed_2949_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2951_, lean_object* v_d_2952_, lean_object* v_b_2953_, uint8_t v_bi_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Expr_forallE___override(v_n_2951_, v_d_2952_, v_b_2953_, v_bi_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2956_, lean_object* v_d_2957_, lean_object* v_b_2958_, lean_object* v_bi_2959_){
_start:
{
uint8_t v_bi_boxed_2960_; lean_object* v_res_2961_; 
v_bi_boxed_2960_ = lean_unbox(v_bi_2959_);
v_res_2961_ = lean_expr_mk_forall(v_n_2956_, v_d_2957_, v_b_2958_, v_bi_boxed_2960_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2962_, lean_object* v_t_2963_, lean_object* v_v_2964_, lean_object* v_b_2965_, uint8_t v_nondep_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_Expr_letE___override(v_n_2962_, v_t_2963_, v_v_2964_, v_b_2965_, v_nondep_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2968_, lean_object* v_t_2969_, lean_object* v_v_2970_, lean_object* v_b_2971_, lean_object* v_nondep_2972_){
_start:
{
uint8_t v_nondep_boxed_2973_; lean_object* v_res_2974_; 
v_nondep_boxed_2973_ = lean_unbox(v_nondep_2972_);
v_res_2974_ = lean_expr_mk_let(v_n_2968_, v_t_2969_, v_v_2970_, v_b_2971_, v_nondep_boxed_2973_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_Lean_Expr_lit___override(v_l_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_2977_, lean_object* v_e_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Expr_mdata___override(v_m_2977_, v_e_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_2980_, lean_object* v_idx_2981_, lean_object* v_struct_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_Expr_proj___override(v_structName_2980_, v_idx_2981_, v_struct_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_2984_, size_t v_i_2985_, size_t v_stop_2986_, lean_object* v_b_2987_){
_start:
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_usize_dec_eq(v_i_2985_, v_stop_2986_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; size_t v___x_2991_; size_t v___x_2992_; 
v___x_2989_ = lean_array_uget_borrowed(v_as_2984_, v_i_2985_);
lean_inc(v___x_2989_);
v___x_2990_ = l_Lean_Expr_app___override(v_b_2987_, v___x_2989_);
v___x_2991_ = ((size_t)1ULL);
v___x_2992_ = lean_usize_add(v_i_2985_, v___x_2991_);
v_i_2985_ = v___x_2992_;
v_b_2987_ = v___x_2990_;
goto _start;
}
else
{
return v_b_2987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_2994_, lean_object* v_i_2995_, lean_object* v_stop_2996_, lean_object* v_b_2997_){
_start:
{
size_t v_i_boxed_2998_; size_t v_stop_boxed_2999_; lean_object* v_res_3000_; 
v_i_boxed_2998_ = lean_unbox_usize(v_i_2995_);
lean_dec(v_i_2995_);
v_stop_boxed_2999_ = lean_unbox_usize(v_stop_2996_);
lean_dec(v_stop_2996_);
v_res_3000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_2994_, v_i_boxed_2998_, v_stop_boxed_2999_, v_b_2997_);
lean_dec_ref(v_as_2994_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3001_, lean_object* v_args_3002_){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3003_ = lean_unsigned_to_nat(0u);
v___x_3004_ = lean_array_get_size(v_args_3002_);
v___x_3005_ = lean_nat_dec_lt(v___x_3003_, v___x_3004_);
if (v___x_3005_ == 0)
{
return v_f_3001_;
}
else
{
size_t v___x_3006_; size_t v___x_3007_; lean_object* v___x_3008_; 
v___x_3006_ = ((size_t)0ULL);
v___x_3007_ = lean_usize_of_nat(v___x_3004_);
v___x_3008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3002_, v___x_3006_, v___x_3007_, v_f_3001_);
return v___x_3008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3009_, lean_object* v_args_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_mkAppN(v_f_3009_, v_args_3010_);
lean_dec_ref(v_args_3010_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3012_, lean_object* v_args_3013_, lean_object* v_i_3014_, lean_object* v_e_3015_){
_start:
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_nat_dec_lt(v_i_3014_, v_n_3012_);
if (v___x_3016_ == 0)
{
lean_dec(v_i_3014_);
return v_e_3015_;
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3017_ = l_Lean_instInhabitedExpr;
v___x_3018_ = lean_unsigned_to_nat(1u);
v___x_3019_ = lean_nat_add(v_i_3014_, v___x_3018_);
v___x_3020_ = lean_array_get_borrowed(v___x_3017_, v_args_3013_, v_i_3014_);
lean_dec(v_i_3014_);
lean_inc(v___x_3020_);
v___x_3021_ = l_Lean_Expr_app___override(v_e_3015_, v___x_3020_);
v_i_3014_ = v___x_3019_;
v_e_3015_ = v___x_3021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3023_, lean_object* v_args_3024_, lean_object* v_i_3025_, lean_object* v_e_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3023_, v_args_3024_, v_i_3025_, v_e_3026_);
lean_dec_ref(v_args_3024_);
lean_dec(v_n_3023_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3028_, lean_object* v_i_3029_, lean_object* v_j_3030_, lean_object* v_args_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3030_, v_args_3031_, v_i_3029_, v_f_3028_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3033_, lean_object* v_i_3034_, lean_object* v_j_3035_, lean_object* v_args_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_mkAppRange(v_f_3033_, v_i_3034_, v_j_3035_, v_args_3036_);
lean_dec_ref(v_args_3036_);
lean_dec(v_j_3035_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3038_, size_t v_i_3039_, size_t v_stop_3040_, lean_object* v_b_3041_){
_start:
{
uint8_t v___x_3042_; 
v___x_3042_ = lean_usize_dec_eq(v_i_3039_, v_stop_3040_);
if (v___x_3042_ == 0)
{
size_t v___x_3043_; size_t v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3043_ = ((size_t)1ULL);
v___x_3044_ = lean_usize_sub(v_i_3039_, v___x_3043_);
v___x_3045_ = lean_array_uget_borrowed(v_as_3038_, v___x_3044_);
lean_inc(v___x_3045_);
v___x_3046_ = l_Lean_Expr_app___override(v_b_3041_, v___x_3045_);
v_i_3039_ = v___x_3044_;
v_b_3041_ = v___x_3046_;
goto _start;
}
else
{
return v_b_3041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3048_, lean_object* v_i_3049_, lean_object* v_stop_3050_, lean_object* v_b_3051_){
_start:
{
size_t v_i_boxed_3052_; size_t v_stop_boxed_3053_; lean_object* v_res_3054_; 
v_i_boxed_3052_ = lean_unbox_usize(v_i_3049_);
lean_dec(v_i_3049_);
v_stop_boxed_3053_ = lean_unbox_usize(v_stop_3050_);
lean_dec(v_stop_3050_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3048_, v_i_boxed_3052_, v_stop_boxed_3053_, v_b_3051_);
lean_dec_ref(v_as_3048_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3055_, lean_object* v_revArgs_3056_){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3057_ = lean_array_get_size(v_revArgs_3056_);
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = lean_nat_dec_lt(v___x_3058_, v___x_3057_);
if (v___x_3059_ == 0)
{
return v_fn_3055_;
}
else
{
size_t v___x_3060_; size_t v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = lean_usize_of_nat(v___x_3057_);
v___x_3061_ = ((size_t)0ULL);
v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3056_, v___x_3060_, v___x_3061_, v_fn_3055_);
return v___x_3062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3063_, lean_object* v_revArgs_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_mkAppRev(v_fn_3063_, v_revArgs_3064_);
lean_dec_ref(v_revArgs_3064_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = lean_expr_dbg_to_string(v_e_3067_);
lean_dec_ref(v_e_3067_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3071_, lean_object* v_b_3072_){
_start:
{
uint8_t v_res_3073_; lean_object* v_r_3074_; 
v_res_3073_ = lean_expr_quick_lt(v_a_3071_, v_b_3072_);
lean_dec_ref(v_b_3072_);
lean_dec_ref(v_a_3071_);
v_r_3074_ = lean_box(v_res_3073_);
return v_r_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3077_, lean_object* v_b_3078_){
_start:
{
uint8_t v_res_3079_; lean_object* v_r_3080_; 
v_res_3079_ = lean_expr_lt(v_a_3077_, v_b_3078_);
lean_dec_ref(v_b_3078_);
lean_dec_ref(v_a_3077_);
v_r_3080_ = lean_box(v_res_3079_);
return v_r_3080_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3081_, lean_object* v_b_3082_){
_start:
{
uint8_t v___x_3083_; 
v___x_3083_ = lean_expr_quick_lt(v_a_3081_, v_b_3082_);
if (v___x_3083_ == 0)
{
uint8_t v___x_3084_; 
v___x_3084_ = lean_expr_quick_lt(v_b_3082_, v_a_3081_);
if (v___x_3084_ == 0)
{
uint8_t v___x_3085_; 
v___x_3085_ = 1;
return v___x_3085_;
}
else
{
uint8_t v___x_3086_; 
v___x_3086_ = 2;
return v___x_3086_;
}
}
else
{
uint8_t v___x_3087_; 
v___x_3087_ = 0;
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3088_, lean_object* v_b_3089_){
_start:
{
uint8_t v_res_3090_; lean_object* v_r_3091_; 
v_res_3090_ = l_Lean_Expr_quickComp(v_a_3088_, v_b_3089_);
lean_dec_ref(v_b_3089_);
lean_dec_ref(v_a_3088_);
v_r_3091_ = lean_box(v_res_3090_);
return v_r_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3094_, lean_object* v_b_3095_){
_start:
{
uint8_t v_res_3096_; lean_object* v_r_3097_; 
v_res_3096_ = lean_expr_eqv(v_a_3094_, v_b_3095_);
lean_dec_ref(v_b_3095_);
lean_dec_ref(v_a_3094_);
v_r_3097_ = lean_box(v_res_3096_);
return v_r_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3102_, lean_object* v_b_3103_){
_start:
{
uint8_t v_res_3104_; lean_object* v_r_3105_; 
v_res_3104_ = lean_expr_equal(v_a_3102_, v_b_3103_);
lean_dec_ref(v_b_3103_);
lean_dec_ref(v_a_3102_);
v_r_3105_ = lean_box(v_res_3104_);
return v_r_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqvBudgeted___boxed(lean_object* v_a_3110_, lean_object* v_b_3111_, lean_object* v_budget_3112_, lean_object* v_a_00___x40___internal___hyg_3113_){
_start:
{
size_t v_budget_boxed_3114_; uint8_t v_res_3115_; lean_object* v_r_3116_; 
v_budget_boxed_3114_ = lean_unbox_usize(v_budget_3112_);
lean_dec(v_budget_3112_);
v_res_3115_ = lean_expr_eqv_budgeted(v_a_3110_, v_b_3111_, v_budget_boxed_3114_);
lean_dec_ref(v_b_3111_);
lean_dec_ref(v_a_3110_);
v_r_3116_ = lean_box(v_res_3115_);
return v_r_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equalBudgeted___boxed(lean_object* v_a_3121_, lean_object* v_b_3122_, lean_object* v_budget_3123_, lean_object* v_a_00___x40___internal___hyg_3124_){
_start:
{
size_t v_budget_boxed_3125_; uint8_t v_res_3126_; lean_object* v_r_3127_; 
v_budget_boxed_3125_ = lean_unbox_usize(v_budget_3123_);
lean_dec(v_budget_3123_);
v_res_3126_ = lean_expr_equal_budgeted(v_a_3121_, v_b_3122_, v_budget_boxed_3125_);
lean_dec_ref(v_b_3122_);
lean_dec_ref(v_a_3121_);
v_r_3127_ = lean_box(v_res_3126_);
return v_r_3127_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3128_){
_start:
{
if (lean_obj_tag(v_x_3128_) == 3)
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3131_){
_start:
{
uint8_t v_res_3132_; lean_object* v_r_3133_; 
v_res_3132_ = l_Lean_Expr_isSort(v_x_3131_);
lean_dec_ref(v_x_3131_);
v_r_3133_ = lean_box(v_res_3132_);
return v_r_3133_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3134_){
_start:
{
if (lean_obj_tag(v_x_3134_) == 3)
{
lean_object* v_u_3135_; 
v_u_3135_ = lean_ctor_get(v_x_3134_, 0);
if (lean_obj_tag(v_u_3135_) == 1)
{
uint8_t v___x_3136_; 
v___x_3136_ = 1;
return v___x_3136_;
}
else
{
uint8_t v___x_3137_; 
v___x_3137_ = 0;
return v___x_3137_;
}
}
else
{
uint8_t v___x_3138_; 
v___x_3138_ = 0;
return v___x_3138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3139_){
_start:
{
uint8_t v_res_3140_; lean_object* v_r_3141_; 
v_res_3140_ = l_Lean_Expr_isType(v_x_3139_);
lean_dec_ref(v_x_3139_);
v_r_3141_ = lean_box(v_res_3140_);
return v_r_3141_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3142_){
_start:
{
if (lean_obj_tag(v_x_3142_) == 3)
{
lean_object* v_u_3143_; 
v_u_3143_ = lean_ctor_get(v_x_3142_, 0);
if (lean_obj_tag(v_u_3143_) == 1)
{
lean_object* v_a_3144_; 
v_a_3144_ = lean_ctor_get(v_u_3143_, 0);
if (lean_obj_tag(v_a_3144_) == 0)
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
else
{
uint8_t v___x_3147_; 
v___x_3147_ = 0;
return v___x_3147_;
}
}
else
{
uint8_t v___x_3148_; 
v___x_3148_ = 0;
return v___x_3148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3149_){
_start:
{
uint8_t v_res_3150_; lean_object* v_r_3151_; 
v_res_3150_ = l_Lean_Expr_isType0(v_x_3149_);
lean_dec_ref(v_x_3149_);
v_r_3151_ = lean_box(v_res_3150_);
return v_r_3151_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3152_){
_start:
{
if (lean_obj_tag(v_x_3152_) == 3)
{
lean_object* v_u_3153_; 
v_u_3153_ = lean_ctor_get(v_x_3152_, 0);
if (lean_obj_tag(v_u_3153_) == 0)
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
else
{
uint8_t v___x_3156_; 
v___x_3156_ = 0;
return v___x_3156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3157_){
_start:
{
uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_res_3158_ = l_Lean_Expr_isProp(v_x_3157_);
lean_dec_ref(v_x_3157_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3160_){
_start:
{
if (lean_obj_tag(v_x_3160_) == 0)
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3163_){
_start:
{
uint8_t v_res_3164_; lean_object* v_r_3165_; 
v_res_3164_ = l_Lean_Expr_isBVar(v_x_3163_);
lean_dec_ref(v_x_3163_);
v_r_3165_ = lean_box(v_res_3164_);
return v_r_3165_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3166_){
_start:
{
if (lean_obj_tag(v_x_3166_) == 2)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3169_){
_start:
{
uint8_t v_res_3170_; lean_object* v_r_3171_; 
v_res_3170_ = l_Lean_Expr_isMVar(v_x_3169_);
lean_dec_ref(v_x_3169_);
v_r_3171_ = lean_box(v_res_3170_);
return v_r_3171_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3172_){
_start:
{
if (lean_obj_tag(v_x_3172_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3175_){
_start:
{
uint8_t v_res_3176_; lean_object* v_r_3177_; 
v_res_3176_ = l_Lean_Expr_isFVar(v_x_3175_);
lean_dec_ref(v_x_3175_);
v_r_3177_ = lean_box(v_res_3176_);
return v_r_3177_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3178_){
_start:
{
if (lean_obj_tag(v_x_3178_) == 5)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3181_){
_start:
{
uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_res_3182_ = l_Lean_Expr_isApp(v_x_3181_);
lean_dec_ref(v_x_3181_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3184_){
_start:
{
if (lean_obj_tag(v_x_3184_) == 11)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3187_){
_start:
{
uint8_t v_res_3188_; lean_object* v_r_3189_; 
v_res_3188_ = l_Lean_Expr_isProj(v_x_3187_);
lean_dec_ref(v_x_3187_);
v_r_3189_ = lean_box(v_res_3188_);
return v_r_3189_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3190_){
_start:
{
if (lean_obj_tag(v_x_3190_) == 4)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3193_){
_start:
{
uint8_t v_res_3194_; lean_object* v_r_3195_; 
v_res_3194_ = l_Lean_Expr_isConst(v_x_3193_);
lean_dec_ref(v_x_3193_);
v_r_3195_ = lean_box(v_res_3194_);
return v_r_3195_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3196_, lean_object* v_x_3197_){
_start:
{
if (lean_obj_tag(v_x_3196_) == 4)
{
lean_object* v_declName_3198_; uint8_t v___x_3199_; 
v_declName_3198_ = lean_ctor_get(v_x_3196_, 0);
v___x_3199_ = lean_name_eq(v_declName_3198_, v_x_3197_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3201_, lean_object* v_x_3202_){
_start:
{
uint8_t v_res_3203_; lean_object* v_r_3204_; 
v_res_3203_ = l_Lean_Expr_isConstOf(v_x_3201_, v_x_3202_);
lean_dec(v_x_3202_);
lean_dec_ref(v_x_3201_);
v_r_3204_ = lean_box(v_res_3203_);
return v_r_3204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3205_, lean_object* v_x_3206_){
_start:
{
if (lean_obj_tag(v_x_3205_) == 1)
{
lean_object* v_fvarId_3207_; uint8_t v___x_3208_; 
v_fvarId_3207_ = lean_ctor_get(v_x_3205_, 0);
v___x_3208_ = lean_name_eq(v_fvarId_3207_, v_x_3206_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3210_, lean_object* v_x_3211_){
_start:
{
uint8_t v_res_3212_; lean_object* v_r_3213_; 
v_res_3212_ = l_Lean_Expr_isFVarOf(v_x_3210_, v_x_3211_);
lean_dec(v_x_3211_);
lean_dec_ref(v_x_3210_);
v_r_3213_ = lean_box(v_res_3212_);
return v_r_3213_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3214_){
_start:
{
if (lean_obj_tag(v_x_3214_) == 7)
{
uint8_t v___x_3215_; 
v___x_3215_ = 1;
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
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3217_){
_start:
{
uint8_t v_res_3218_; lean_object* v_r_3219_; 
v_res_3218_ = l_Lean_Expr_isForall(v_x_3217_);
lean_dec_ref(v_x_3217_);
v_r_3219_ = lean_box(v_res_3218_);
return v_r_3219_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3220_){
_start:
{
if (lean_obj_tag(v_x_3220_) == 6)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3223_){
_start:
{
uint8_t v_res_3224_; lean_object* v_r_3225_; 
v_res_3224_ = l_Lean_Expr_isLambda(v_x_3223_);
lean_dec_ref(v_x_3223_);
v_r_3225_ = lean_box(v_res_3224_);
return v_r_3225_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3226_){
_start:
{
switch(lean_obj_tag(v_x_3226_))
{
case 6:
{
uint8_t v___x_3227_; 
v___x_3227_ = 1;
return v___x_3227_;
}
case 7:
{
uint8_t v___x_3228_; 
v___x_3228_ = 1;
return v___x_3228_;
}
default: 
{
uint8_t v___x_3229_; 
v___x_3229_ = 0;
return v___x_3229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3230_){
_start:
{
uint8_t v_res_3231_; lean_object* v_r_3232_; 
v_res_3231_ = l_Lean_Expr_isBinding(v_x_3230_);
lean_dec_ref(v_x_3230_);
v_r_3232_ = lean_box(v_res_3231_);
return v_r_3232_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3233_){
_start:
{
if (lean_obj_tag(v_x_3233_) == 8)
{
uint8_t v___x_3234_; 
v___x_3234_ = 1;
return v___x_3234_;
}
else
{
uint8_t v___x_3235_; 
v___x_3235_ = 0;
return v___x_3235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3236_){
_start:
{
uint8_t v_res_3237_; lean_object* v_r_3238_; 
v_res_3237_ = l_Lean_Expr_isLet(v_x_3236_);
lean_dec_ref(v_x_3236_);
v_r_3238_ = lean_box(v_res_3237_);
return v_r_3238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3239_){
_start:
{
if (lean_obj_tag(v_x_3239_) == 8)
{
uint8_t v_nondep_3240_; 
v_nondep_3240_ = lean_ctor_get_uint8(v_x_3239_, sizeof(void*)*4 + 8);
return v_nondep_3240_;
}
else
{
uint8_t v___x_3241_; 
v___x_3241_ = 0;
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3242_){
_start:
{
uint8_t v_res_3243_; lean_object* v_r_3244_; 
v_res_3243_ = l_Lean_Expr_isHave(v_x_3242_);
lean_dec_ref(v_x_3242_);
v_r_3244_ = lean_box(v_res_3243_);
return v_r_3244_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3245_){
_start:
{
uint8_t v___x_3246_; 
v___x_3246_ = l_Lean_Expr_isHave(v_a_3245_);
lean_dec_ref(v_a_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3247_){
_start:
{
uint8_t v_res_3248_; lean_object* v_r_3249_; 
v_res_3248_ = lean_expr_is_have(v_a_3247_);
v_r_3249_ = lean_box(v_res_3248_);
return v_r_3249_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3250_){
_start:
{
if (lean_obj_tag(v_x_3250_) == 10)
{
uint8_t v___x_3251_; 
v___x_3251_ = 1;
return v___x_3251_;
}
else
{
uint8_t v___x_3252_; 
v___x_3252_ = 0;
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3253_){
_start:
{
uint8_t v_res_3254_; lean_object* v_r_3255_; 
v_res_3254_ = l_Lean_Expr_isMData(v_x_3253_);
lean_dec_ref(v_x_3253_);
v_r_3255_ = lean_box(v_res_3254_);
return v_r_3255_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3256_){
_start:
{
if (lean_obj_tag(v_x_3256_) == 9)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3259_){
_start:
{
uint8_t v_res_3260_; lean_object* v_r_3261_; 
v_res_3260_ = l_Lean_Expr_isLit(v_x_3259_);
lean_dec_ref(v_x_3259_);
v_r_3261_ = lean_box(v_res_3260_);
return v_r_3261_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3262_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = l_Lean_instInhabitedExpr;
v___x_3264_ = lean_panic_fn_borrowed(v___x_3263_, v_msg_3262_);
return v___x_3264_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3268_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3269_ = lean_unsigned_to_nat(15u);
v___x_3270_ = lean_unsigned_to_nat(974u);
v___x_3271_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3272_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3273_ = l_mkPanicMessageWithDecl(v___x_3272_, v___x_3271_, v___x_3270_, v___x_3269_, v___x_3268_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3274_){
_start:
{
if (lean_obj_tag(v_x_3274_) == 5)
{
lean_object* v_fn_3275_; 
v_fn_3275_ = lean_ctor_get(v_x_3274_, 0);
lean_inc_ref(v_fn_3275_);
return v_fn_3275_;
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3277_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3276_);
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Lean_Expr_appFn_x21(v_x_3278_);
lean_dec_ref(v_x_3278_);
return v_res_3279_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3281_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3282_ = lean_unsigned_to_nat(15u);
v___x_3283_ = lean_unsigned_to_nat(978u);
v___x_3284_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3285_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3286_ = l_mkPanicMessageWithDecl(v___x_3285_, v___x_3284_, v___x_3283_, v___x_3282_, v___x_3281_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3287_){
_start:
{
if (lean_obj_tag(v_x_3287_) == 5)
{
lean_object* v_arg_3288_; 
v_arg_3288_ = lean_ctor_get(v_x_3287_, 1);
lean_inc_ref(v_arg_3288_);
return v_arg_3288_;
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3290_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3289_);
return v___x_3290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_Lean_Expr_appArg_x21(v_x_3291_);
lean_dec_ref(v_x_3291_);
return v_res_3292_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3294_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3295_ = lean_unsigned_to_nat(17u);
v___x_3296_ = lean_unsigned_to_nat(983u);
v___x_3297_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3298_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3299_ = l_mkPanicMessageWithDecl(v___x_3298_, v___x_3297_, v___x_3296_, v___x_3295_, v___x_3294_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3300_){
_start:
{
switch(lean_obj_tag(v_x_3300_))
{
case 10:
{
lean_object* v_expr_3301_; 
v_expr_3301_ = lean_ctor_get(v_x_3300_, 1);
v_x_3300_ = v_expr_3301_;
goto _start;
}
case 5:
{
lean_object* v_fn_3303_; 
v_fn_3303_ = lean_ctor_get(v_x_3300_, 0);
lean_inc_ref(v_fn_3303_);
return v_fn_3303_;
}
default: 
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3305_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3304_);
return v___x_3305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_Expr_appFn_x21_x27(v_x_3306_);
lean_dec_ref(v_x_3306_);
return v_res_3307_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3309_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3310_ = lean_unsigned_to_nat(17u);
v___x_3311_ = lean_unsigned_to_nat(988u);
v___x_3312_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3313_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3314_ = l_mkPanicMessageWithDecl(v___x_3313_, v___x_3312_, v___x_3311_, v___x_3310_, v___x_3309_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3315_){
_start:
{
switch(lean_obj_tag(v_x_3315_))
{
case 10:
{
lean_object* v_expr_3316_; 
v_expr_3316_ = lean_ctor_get(v_x_3315_, 1);
v_x_3315_ = v_expr_3316_;
goto _start;
}
case 5:
{
lean_object* v_arg_3318_; 
v_arg_3318_ = lean_ctor_get(v_x_3315_, 1);
lean_inc_ref(v_arg_3318_);
return v_arg_3318_;
}
default: 
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3320_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3319_);
return v___x_3320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Expr_appArg_x21_x27(v_x_3321_);
lean_dec_ref(v_x_3321_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3323_){
_start:
{
lean_object* v_arg_3324_; 
v_arg_3324_ = lean_ctor_get(v_e_3323_, 1);
lean_inc_ref(v_arg_3324_);
return v_arg_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_Expr_appArg___redArg(v_e_3325_);
lean_dec_ref(v_e_3325_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3327_, lean_object* v_h_3328_){
_start:
{
lean_object* v_arg_3329_; 
v_arg_3329_ = lean_ctor_get(v_e_3327_, 1);
lean_inc_ref(v_arg_3329_);
return v_arg_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3330_, lean_object* v_h_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_Expr_appArg(v_e_3330_, v_h_3331_);
lean_dec_ref(v_e_3330_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3333_){
_start:
{
lean_object* v_fn_3334_; 
v_fn_3334_ = lean_ctor_get(v_e_3333_, 0);
lean_inc_ref(v_fn_3334_);
return v_fn_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_Expr_appFn___redArg(v_e_3335_);
lean_dec_ref(v_e_3335_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3337_, lean_object* v_h_3338_){
_start:
{
lean_object* v_fn_3339_; 
v_fn_3339_ = lean_ctor_get(v_e_3337_, 0);
lean_inc_ref(v_fn_3339_);
return v_fn_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3340_, lean_object* v_h_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Expr_appFn(v_e_3340_, v_h_3341_);
lean_dec_ref(v_e_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3343_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_panic_fn_borrowed(v___x_3344_, v_msg_3343_);
return v___x_3345_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3348_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3349_ = lean_unsigned_to_nat(14u);
v___x_3350_ = lean_unsigned_to_nat(1000u);
v___x_3351_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3352_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3353_ = l_mkPanicMessageWithDecl(v___x_3352_, v___x_3351_, v___x_3350_, v___x_3349_, v___x_3348_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3354_){
_start:
{
if (lean_obj_tag(v_x_3354_) == 3)
{
lean_object* v_u_3355_; 
v_u_3355_ = lean_ctor_get(v_x_3354_, 0);
lean_inc(v_u_3355_);
return v_u_3355_;
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3357_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3356_);
return v___x_3357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_Expr_sortLevel_x21(v_x_3358_);
lean_dec_ref(v_x_3358_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3360_){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3362_ = lean_panic_fn_borrowed(v___x_3361_, v_msg_3360_);
return v___x_3362_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3365_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3366_ = lean_unsigned_to_nat(13u);
v___x_3367_ = lean_unsigned_to_nat(1004u);
v___x_3368_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3369_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3370_ = l_mkPanicMessageWithDecl(v___x_3369_, v___x_3368_, v___x_3367_, v___x_3366_, v___x_3365_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3371_){
_start:
{
if (lean_obj_tag(v_x_3371_) == 9)
{
lean_object* v_a_3372_; 
v_a_3372_ = lean_ctor_get(v_x_3371_, 0);
lean_inc_ref(v_a_3372_);
return v_a_3372_;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3374_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3373_);
return v___x_3374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_Expr_litValue_x21(v_x_3375_);
lean_dec_ref(v_x_3375_);
return v_res_3376_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3377_){
_start:
{
if (lean_obj_tag(v_x_3377_) == 9)
{
lean_object* v_a_3378_; 
v_a_3378_ = lean_ctor_get(v_x_3377_, 0);
if (lean_obj_tag(v_a_3378_) == 0)
{
uint8_t v___x_3379_; 
v___x_3379_ = 1;
return v___x_3379_;
}
else
{
uint8_t v___x_3380_; 
v___x_3380_ = 0;
return v___x_3380_;
}
}
else
{
uint8_t v___x_3381_; 
v___x_3381_ = 0;
return v___x_3381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3382_){
_start:
{
uint8_t v_res_3383_; lean_object* v_r_3384_; 
v_res_3383_ = l_Lean_Expr_isRawNatLit(v_x_3382_);
lean_dec_ref(v_x_3382_);
v_r_3384_ = lean_box(v_res_3383_);
return v_r_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3385_){
_start:
{
if (lean_obj_tag(v_x_3385_) == 9)
{
lean_object* v_a_3386_; 
v_a_3386_ = lean_ctor_get(v_x_3385_, 0);
lean_inc_ref(v_a_3386_);
lean_dec_ref_known(v_x_3385_, 1);
if (lean_obj_tag(v_a_3386_) == 0)
{
lean_object* v_val_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
v_val_3387_ = lean_ctor_get(v_a_3386_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_a_3386_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v_a_3386_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_val_3387_);
lean_dec(v_a_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set_tag(v___x_3389_, 1);
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_val_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
else
{
lean_object* v___x_3395_; 
lean_dec_ref(v_a_3386_);
v___x_3395_ = lean_box(0);
return v___x_3395_;
}
}
else
{
lean_object* v___x_3396_; 
lean_dec_ref(v_x_3385_);
v___x_3396_ = lean_box(0);
return v___x_3396_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3397_){
_start:
{
if (lean_obj_tag(v_x_3397_) == 9)
{
lean_object* v_a_3398_; 
v_a_3398_ = lean_ctor_get(v_x_3397_, 0);
if (lean_obj_tag(v_a_3398_) == 1)
{
uint8_t v___x_3399_; 
v___x_3399_ = 1;
return v___x_3399_;
}
else
{
uint8_t v___x_3400_; 
v___x_3400_ = 0;
return v___x_3400_;
}
}
else
{
uint8_t v___x_3401_; 
v___x_3401_ = 0;
return v___x_3401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3402_){
_start:
{
uint8_t v_res_3403_; lean_object* v_r_3404_; 
v_res_3403_ = l_Lean_Expr_isStringLit(v_x_3402_);
lean_dec_ref(v_x_3402_);
v_r_3404_ = lean_box(v_res_3403_);
return v_r_3404_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3409_){
_start:
{
if (lean_obj_tag(v_x_3409_) == 5)
{
lean_object* v_fn_3410_; 
v_fn_3410_ = lean_ctor_get(v_x_3409_, 0);
if (lean_obj_tag(v_fn_3410_) == 4)
{
lean_object* v_arg_3411_; lean_object* v_declName_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v_arg_3411_ = lean_ctor_get(v_x_3409_, 1);
v_declName_3412_ = lean_ctor_get(v_fn_3410_, 0);
v___x_3413_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3414_ = lean_name_eq(v_declName_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
return v___x_3414_;
}
else
{
uint8_t v___x_3415_; 
v___x_3415_ = l_Lean_Expr_isRawNatLit(v_arg_3411_);
return v___x_3415_;
}
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
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3418_){
_start:
{
uint8_t v_res_3419_; lean_object* v_r_3420_; 
v_res_3419_ = l_Lean_Expr_isCharLit(v_x_3418_);
lean_dec_ref(v_x_3418_);
v_r_3420_ = lean_box(v_res_3419_);
return v_r_3420_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3421_){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = lean_box(0);
v___x_3423_ = lean_panic_fn_borrowed(v___x_3422_, v_msg_3421_);
return v___x_3423_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3426_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3427_ = lean_unsigned_to_nat(17u);
v___x_3428_ = lean_unsigned_to_nat(1028u);
v___x_3429_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3430_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3431_ = l_mkPanicMessageWithDecl(v___x_3430_, v___x_3429_, v___x_3428_, v___x_3427_, v___x_3426_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3432_){
_start:
{
if (lean_obj_tag(v_x_3432_) == 4)
{
lean_object* v_declName_3433_; 
v_declName_3433_ = lean_ctor_get(v_x_3432_, 0);
lean_inc(v_declName_3433_);
return v_declName_3433_;
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3435_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3434_);
return v___x_3435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Expr_constName_x21(v_x_3436_);
lean_dec_ref(v_x_3436_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3438_){
_start:
{
if (lean_obj_tag(v_x_3438_) == 4)
{
lean_object* v_declName_3439_; lean_object* v___x_3440_; 
v_declName_3439_ = lean_ctor_get(v_x_3438_, 0);
lean_inc(v_declName_3439_);
v___x_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3440_, 0, v_declName_3439_);
return v___x_3440_;
}
else
{
lean_object* v___x_3441_; 
v___x_3441_ = lean_box(0);
return v___x_3441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_Expr_constName_x3f(v_x_3442_);
lean_dec_ref(v_x_3442_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3444_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Lean_Expr_constName_x3f(v_e_3444_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_box(0);
return v___x_3446_;
}
else
{
lean_object* v_val_3447_; 
v_val_3447_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_val_3447_);
lean_dec_ref_known(v___x_3445_, 1);
return v_val_3447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Expr_constName(v_e_3448_);
lean_dec_ref(v_e_3448_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3450_){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_panic_fn_borrowed(v___x_3451_, v_msg_3450_);
return v___x_3452_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3454_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3455_ = lean_unsigned_to_nat(18u);
v___x_3456_ = lean_unsigned_to_nat(1048u);
v___x_3457_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3458_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3459_ = l_mkPanicMessageWithDecl(v___x_3458_, v___x_3457_, v___x_3456_, v___x_3455_, v___x_3454_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3460_){
_start:
{
if (lean_obj_tag(v_x_3460_) == 4)
{
lean_object* v_us_3461_; 
v_us_3461_ = lean_ctor_get(v_x_3460_, 1);
lean_inc(v_us_3461_);
return v_us_3461_;
}
else
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3463_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3462_);
return v___x_3463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_Expr_constLevels_x21(v_x_3464_);
lean_dec_ref(v_x_3464_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3466_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = lean_unsigned_to_nat(0u);
v___x_3468_ = lean_panic_fn_borrowed(v___x_3467_, v_msg_3466_);
return v___x_3468_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3471_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3472_ = lean_unsigned_to_nat(16u);
v___x_3473_ = lean_unsigned_to_nat(1052u);
v___x_3474_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3475_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3476_ = l_mkPanicMessageWithDecl(v___x_3475_, v___x_3474_, v___x_3473_, v___x_3472_, v___x_3471_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3477_){
_start:
{
if (lean_obj_tag(v_x_3477_) == 0)
{
lean_object* v_deBruijnIndex_3478_; 
v_deBruijnIndex_3478_ = lean_ctor_get(v_x_3477_, 0);
lean_inc(v_deBruijnIndex_3478_);
return v_deBruijnIndex_3478_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3480_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3479_);
return v___x_3480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_Expr_bvarIdx_x21(v_x_3481_);
lean_dec_ref(v_x_3481_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3483_){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = lean_box(0);
v___x_3485_ = lean_panic_fn_borrowed(v___x_3484_, v_msg_3483_);
return v___x_3485_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3488_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3489_ = lean_unsigned_to_nat(14u);
v___x_3490_ = lean_unsigned_to_nat(1056u);
v___x_3491_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3492_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3493_ = l_mkPanicMessageWithDecl(v___x_3492_, v___x_3491_, v___x_3490_, v___x_3489_, v___x_3488_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3494_){
_start:
{
if (lean_obj_tag(v_x_3494_) == 1)
{
lean_object* v_fvarId_3495_; 
v_fvarId_3495_ = lean_ctor_get(v_x_3494_, 0);
lean_inc(v_fvarId_3495_);
return v_fvarId_3495_;
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3497_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3496_);
return v___x_3497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_Expr_fvarId_x21(v_x_3498_);
lean_dec_ref(v_x_3498_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3500_){
_start:
{
if (lean_obj_tag(v_x_3500_) == 1)
{
lean_object* v_fvarId_3501_; lean_object* v___x_3502_; 
v_fvarId_3501_ = lean_ctor_get(v_x_3500_, 0);
lean_inc(v_fvarId_3501_);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_fvarId_3501_);
return v___x_3502_;
}
else
{
lean_object* v___x_3503_; 
v___x_3503_ = lean_box(0);
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Lean_Expr_fvarId_x3f(v_x_3504_);
lean_dec_ref(v_x_3504_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3506_){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = lean_box(0);
v___x_3508_ = lean_panic_fn_borrowed(v___x_3507_, v_msg_3506_);
return v___x_3508_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3511_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3512_ = lean_unsigned_to_nat(14u);
v___x_3513_ = lean_unsigned_to_nat(1064u);
v___x_3514_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3515_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3516_ = l_mkPanicMessageWithDecl(v___x_3515_, v___x_3514_, v___x_3513_, v___x_3512_, v___x_3511_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3517_){
_start:
{
if (lean_obj_tag(v_x_3517_) == 2)
{
lean_object* v_mvarId_3518_; 
v_mvarId_3518_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_mvarId_3518_);
return v_mvarId_3518_;
}
else
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3520_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3519_);
return v___x_3520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_Expr_mvarId_x21(v_x_3521_);
lean_dec_ref(v_x_3521_);
return v_res_3522_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3525_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3526_ = lean_unsigned_to_nat(23u);
v___x_3527_ = lean_unsigned_to_nat(1069u);
v___x_3528_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3529_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3530_ = l_mkPanicMessageWithDecl(v___x_3529_, v___x_3528_, v___x_3527_, v___x_3526_, v___x_3525_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3531_){
_start:
{
switch(lean_obj_tag(v_x_3531_))
{
case 7:
{
lean_object* v_binderName_3532_; 
v_binderName_3532_ = lean_ctor_get(v_x_3531_, 0);
lean_inc(v_binderName_3532_);
return v_binderName_3532_;
}
case 6:
{
lean_object* v_binderName_3533_; 
v_binderName_3533_ = lean_ctor_get(v_x_3531_, 0);
lean_inc(v_binderName_3533_);
return v_binderName_3533_;
}
default: 
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3535_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3534_);
return v___x_3535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Expr_bindingName_x21(v_x_3536_);
lean_dec_ref(v_x_3536_);
return v_res_3537_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3539_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3540_ = lean_unsigned_to_nat(23u);
v___x_3541_ = lean_unsigned_to_nat(1074u);
v___x_3542_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3543_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3544_ = l_mkPanicMessageWithDecl(v___x_3543_, v___x_3542_, v___x_3541_, v___x_3540_, v___x_3539_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3545_){
_start:
{
switch(lean_obj_tag(v_x_3545_))
{
case 7:
{
lean_object* v_binderType_3546_; 
v_binderType_3546_ = lean_ctor_get(v_x_3545_, 1);
lean_inc_ref(v_binderType_3546_);
return v_binderType_3546_;
}
case 6:
{
lean_object* v_binderType_3547_; 
v_binderType_3547_ = lean_ctor_get(v_x_3545_, 1);
lean_inc_ref(v_binderType_3547_);
return v_binderType_3547_;
}
default: 
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3549_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3548_);
return v___x_3549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_Lean_Expr_bindingDomain_x21(v_x_3550_);
lean_dec_ref(v_x_3550_);
return v_res_3551_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3553_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3554_ = lean_unsigned_to_nat(23u);
v___x_3555_ = lean_unsigned_to_nat(1079u);
v___x_3556_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3557_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3558_ = l_mkPanicMessageWithDecl(v___x_3557_, v___x_3556_, v___x_3555_, v___x_3554_, v___x_3553_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3559_){
_start:
{
switch(lean_obj_tag(v_x_3559_))
{
case 7:
{
lean_object* v_body_3560_; 
v_body_3560_ = lean_ctor_get(v_x_3559_, 2);
lean_inc_ref(v_body_3560_);
return v_body_3560_;
}
case 6:
{
lean_object* v_body_3561_; 
v_body_3561_ = lean_ctor_get(v_x_3559_, 2);
lean_inc_ref(v_body_3561_);
return v_body_3561_;
}
default: 
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3563_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3562_);
return v___x_3563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_Expr_bindingBody_x21(v_x_3564_);
lean_dec_ref(v_x_3564_);
return v_res_3565_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3566_){
_start:
{
uint8_t v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3567_ = 0;
v___x_3568_ = lean_box(v___x_3567_);
v___x_3569_ = lean_panic_fn_borrowed(v___x_3568_, v_msg_3566_);
lean_dec(v___x_3568_);
v___x_3570_ = lean_unbox(v___x_3569_);
lean_dec(v___x_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3571_){
_start:
{
uint8_t v_res_3572_; lean_object* v_r_3573_; 
v_res_3572_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3571_);
v_r_3573_ = lean_box(v_res_3572_);
return v_r_3573_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3575_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3576_ = lean_unsigned_to_nat(24u);
v___x_3577_ = lean_unsigned_to_nat(1084u);
v___x_3578_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3579_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3580_ = l_mkPanicMessageWithDecl(v___x_3579_, v___x_3578_, v___x_3577_, v___x_3576_, v___x_3575_);
return v___x_3580_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3581_){
_start:
{
switch(lean_obj_tag(v_x_3581_))
{
case 7:
{
uint8_t v_binderInfo_3582_; 
v_binderInfo_3582_ = lean_ctor_get_uint8(v_x_3581_, sizeof(void*)*3 + 8);
return v_binderInfo_3582_;
}
case 6:
{
uint8_t v_binderInfo_3583_; 
v_binderInfo_3583_ = lean_ctor_get_uint8(v_x_3581_, sizeof(void*)*3 + 8);
return v_binderInfo_3583_;
}
default: 
{
lean_object* v___x_3584_; uint8_t v___x_3585_; 
v___x_3584_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3585_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3584_);
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3586_){
_start:
{
uint8_t v_res_3587_; lean_object* v_r_3588_; 
v_res_3587_ = l_Lean_Expr_bindingInfo_x21(v_x_3586_);
lean_dec_ref(v_x_3586_);
v_r_3588_ = lean_box(v_res_3587_);
return v_r_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3589_){
_start:
{
lean_object* v_binderName_3590_; 
v_binderName_3590_ = lean_ctor_get(v_x_3589_, 0);
lean_inc(v_binderName_3590_);
return v_binderName_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Expr_forallName___redArg(v_x_3591_);
lean_dec_ref(v_x_3591_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3593_, lean_object* v_x_3594_){
_start:
{
lean_object* v_binderName_3595_; 
v_binderName_3595_ = lean_ctor_get(v_x_3593_, 0);
lean_inc(v_binderName_3595_);
return v_binderName_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_Expr_forallName(v_x_3596_, v_x_3597_);
lean_dec_ref(v_x_3596_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3599_){
_start:
{
lean_object* v_binderType_3600_; 
v_binderType_3600_ = lean_ctor_get(v_x_3599_, 1);
lean_inc_ref(v_binderType_3600_);
return v_binderType_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_Expr_forallDomain___redArg(v_x_3601_);
lean_dec_ref(v_x_3601_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
lean_object* v_binderType_3605_; 
v_binderType_3605_ = lean_ctor_get(v_x_3603_, 1);
lean_inc_ref(v_binderType_3605_);
return v_binderType_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3606_, lean_object* v_x_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lean_Expr_forallDomain(v_x_3606_, v_x_3607_);
lean_dec_ref(v_x_3606_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3609_){
_start:
{
lean_object* v_body_3610_; 
v_body_3610_ = lean_ctor_get(v_x_3609_, 2);
lean_inc_ref(v_body_3610_);
return v_body_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_Expr_forallBody___redArg(v_x_3611_);
lean_dec_ref(v_x_3611_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3613_, lean_object* v_x_3614_){
_start:
{
lean_object* v_body_3615_; 
v_body_3615_ = lean_ctor_get(v_x_3613_, 2);
lean_inc_ref(v_body_3615_);
return v_body_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3616_, lean_object* v_x_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_Expr_forallBody(v_x_3616_, v_x_3617_);
lean_dec_ref(v_x_3616_);
return v_res_3618_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3619_){
_start:
{
uint8_t v_binderInfo_3620_; 
v_binderInfo_3620_ = lean_ctor_get_uint8(v_x_3619_, sizeof(void*)*3 + 8);
return v_binderInfo_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3621_){
_start:
{
uint8_t v_res_3622_; lean_object* v_r_3623_; 
v_res_3622_ = l_Lean_Expr_forallInfo___redArg(v_x_3621_);
lean_dec_ref(v_x_3621_);
v_r_3623_ = lean_box(v_res_3622_);
return v_r_3623_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
uint8_t v_binderInfo_3626_; 
v_binderInfo_3626_ = lean_ctor_get_uint8(v_x_3624_, sizeof(void*)*3 + 8);
return v_binderInfo_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3627_, lean_object* v_x_3628_){
_start:
{
uint8_t v_res_3629_; lean_object* v_r_3630_; 
v_res_3629_ = l_Lean_Expr_forallInfo(v_x_3627_, v_x_3628_);
lean_dec_ref(v_x_3627_);
v_r_3630_ = lean_box(v_res_3629_);
return v_r_3630_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3633_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3634_ = lean_unsigned_to_nat(17u);
v___x_3635_ = lean_unsigned_to_nat(1100u);
v___x_3636_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3637_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3638_ = l_mkPanicMessageWithDecl(v___x_3637_, v___x_3636_, v___x_3635_, v___x_3634_, v___x_3633_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3639_){
_start:
{
if (lean_obj_tag(v_x_3639_) == 8)
{
lean_object* v_declName_3640_; 
v_declName_3640_ = lean_ctor_get(v_x_3639_, 0);
lean_inc(v_declName_3640_);
return v_declName_3640_;
}
else
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3642_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3641_);
return v___x_3642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Lean_Expr_letName_x21(v_x_3643_);
lean_dec_ref(v_x_3643_);
return v_res_3644_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3646_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3647_ = lean_unsigned_to_nat(19u);
v___x_3648_ = lean_unsigned_to_nat(1104u);
v___x_3649_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3650_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3651_ = l_mkPanicMessageWithDecl(v___x_3650_, v___x_3649_, v___x_3648_, v___x_3647_, v___x_3646_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3652_){
_start:
{
if (lean_obj_tag(v_x_3652_) == 8)
{
lean_object* v_type_3653_; 
v_type_3653_ = lean_ctor_get(v_x_3652_, 1);
lean_inc_ref(v_type_3653_);
return v_type_3653_;
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3655_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3654_);
return v___x_3655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_Lean_Expr_letType_x21(v_x_3656_);
lean_dec_ref(v_x_3656_);
return v_res_3657_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3659_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3660_ = lean_unsigned_to_nat(21u);
v___x_3661_ = lean_unsigned_to_nat(1108u);
v___x_3662_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3663_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3664_ = l_mkPanicMessageWithDecl(v___x_3663_, v___x_3662_, v___x_3661_, v___x_3660_, v___x_3659_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3665_){
_start:
{
if (lean_obj_tag(v_x_3665_) == 8)
{
lean_object* v_value_3666_; 
v_value_3666_ = lean_ctor_get(v_x_3665_, 2);
lean_inc_ref(v_value_3666_);
return v_value_3666_;
}
else
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3668_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3667_);
return v___x_3668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lean_Expr_letValue_x21(v_x_3669_);
lean_dec_ref(v_x_3669_);
return v_res_3670_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3672_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3673_ = lean_unsigned_to_nat(23u);
v___x_3674_ = lean_unsigned_to_nat(1112u);
v___x_3675_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3676_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3677_ = l_mkPanicMessageWithDecl(v___x_3676_, v___x_3675_, v___x_3674_, v___x_3673_, v___x_3672_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3678_){
_start:
{
if (lean_obj_tag(v_x_3678_) == 8)
{
lean_object* v_body_3679_; 
v_body_3679_ = lean_ctor_get(v_x_3678_, 3);
lean_inc_ref(v_body_3679_);
return v_body_3679_;
}
else
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3681_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3680_);
return v___x_3681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Lean_Expr_letBody_x21(v_x_3682_);
lean_dec_ref(v_x_3682_);
return v_res_3683_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3684_){
_start:
{
uint8_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v___x_3685_ = 0;
v___x_3686_ = lean_box(v___x_3685_);
v___x_3687_ = lean_panic_fn_borrowed(v___x_3686_, v_msg_3684_);
lean_dec(v___x_3686_);
v___x_3688_ = lean_unbox(v___x_3687_);
lean_dec(v___x_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3689_){
_start:
{
uint8_t v_res_3690_; lean_object* v_r_3691_; 
v_res_3690_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3689_);
v_r_3691_ = lean_box(v_res_3690_);
return v_r_3691_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3693_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3694_ = lean_unsigned_to_nat(27u);
v___x_3695_ = lean_unsigned_to_nat(1116u);
v___x_3696_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3697_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3698_ = l_mkPanicMessageWithDecl(v___x_3697_, v___x_3696_, v___x_3695_, v___x_3694_, v___x_3693_);
return v___x_3698_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3699_){
_start:
{
if (lean_obj_tag(v_x_3699_) == 8)
{
uint8_t v_nondep_3700_; 
v_nondep_3700_ = lean_ctor_get_uint8(v_x_3699_, sizeof(void*)*4 + 8);
return v_nondep_3700_;
}
else
{
lean_object* v___x_3701_; uint8_t v___x_3702_; 
v___x_3701_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3702_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3701_);
return v___x_3702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3703_){
_start:
{
uint8_t v_res_3704_; lean_object* v_r_3705_; 
v_res_3704_ = l_Lean_Expr_letNondep_x21(v_x_3703_);
lean_dec_ref(v_x_3703_);
v_r_3705_ = lean_box(v_res_3704_);
return v_r_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3706_){
_start:
{
if (lean_obj_tag(v_x_3706_) == 10)
{
lean_object* v_expr_3707_; 
v_expr_3707_ = lean_ctor_get(v_x_3706_, 1);
v_x_3706_ = v_expr_3707_;
goto _start;
}
else
{
lean_inc_ref(v_x_3706_);
return v_x_3706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_Expr_consumeMData(v_x_3709_);
lean_dec_ref(v_x_3709_);
return v_res_3710_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3713_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3714_ = lean_unsigned_to_nat(17u);
v___x_3715_ = lean_unsigned_to_nat(1124u);
v___x_3716_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3717_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3718_ = l_mkPanicMessageWithDecl(v___x_3717_, v___x_3716_, v___x_3715_, v___x_3714_, v___x_3713_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3719_){
_start:
{
if (lean_obj_tag(v_x_3719_) == 10)
{
lean_object* v_expr_3720_; 
v_expr_3720_ = lean_ctor_get(v_x_3719_, 1);
lean_inc_ref(v_expr_3720_);
return v_expr_3720_;
}
else
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3722_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3721_);
return v___x_3722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_Expr_mdataExpr_x21(v_x_3723_);
lean_dec_ref(v_x_3723_);
return v_res_3724_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3727_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3728_ = lean_unsigned_to_nat(18u);
v___x_3729_ = lean_unsigned_to_nat(1128u);
v___x_3730_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3731_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3732_ = l_mkPanicMessageWithDecl(v___x_3731_, v___x_3730_, v___x_3729_, v___x_3728_, v___x_3727_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3733_){
_start:
{
if (lean_obj_tag(v_x_3733_) == 11)
{
lean_object* v_struct_3734_; 
v_struct_3734_ = lean_ctor_get(v_x_3733_, 2);
lean_inc_ref(v_struct_3734_);
return v_struct_3734_;
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3735_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3736_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3735_);
return v___x_3736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l_Lean_Expr_projExpr_x21(v_x_3737_);
lean_dec_ref(v_x_3737_);
return v_res_3738_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3740_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3741_ = lean_unsigned_to_nat(18u);
v___x_3742_ = lean_unsigned_to_nat(1132u);
v___x_3743_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3744_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3745_ = l_mkPanicMessageWithDecl(v___x_3744_, v___x_3743_, v___x_3742_, v___x_3741_, v___x_3740_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3746_){
_start:
{
if (lean_obj_tag(v_x_3746_) == 11)
{
lean_object* v_idx_3747_; 
v_idx_3747_ = lean_ctor_get(v_x_3746_, 1);
lean_inc(v_idx_3747_);
return v_idx_3747_;
}
else
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3748_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3749_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3748_);
return v___x_3749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_Lean_Expr_projIdx_x21(v_x_3750_);
lean_dec_ref(v_x_3750_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3752_){
_start:
{
if (lean_obj_tag(v_x_3752_) == 7)
{
lean_object* v_body_3753_; 
v_body_3753_ = lean_ctor_get(v_x_3752_, 2);
v_x_3752_ = v_body_3753_;
goto _start;
}
else
{
lean_inc_ref(v_x_3752_);
return v_x_3752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l_Lean_Expr_getForallBody(v_x_3755_);
lean_dec_ref(v_x_3755_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3757_, lean_object* v_x_3758_){
_start:
{
lean_object* v_zero_3759_; uint8_t v_isZero_3760_; 
v_zero_3759_ = lean_unsigned_to_nat(0u);
v_isZero_3760_ = lean_nat_dec_eq(v_x_3757_, v_zero_3759_);
if (v_isZero_3760_ == 1)
{
lean_dec(v_x_3757_);
lean_inc_ref(v_x_3758_);
return v_x_3758_;
}
else
{
if (lean_obj_tag(v_x_3758_) == 7)
{
lean_object* v_body_3761_; lean_object* v_one_3762_; lean_object* v_n_3763_; 
v_body_3761_ = lean_ctor_get(v_x_3758_, 2);
v_one_3762_ = lean_unsigned_to_nat(1u);
v_n_3763_ = lean_nat_sub(v_x_3757_, v_one_3762_);
lean_dec(v_x_3757_);
v_x_3757_ = v_n_3763_;
v_x_3758_ = v_body_3761_;
goto _start;
}
else
{
lean_dec(v_x_3757_);
lean_inc_ref(v_x_3758_);
return v_x_3758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3765_, lean_object* v_x_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3765_, v_x_3766_);
lean_dec_ref(v_x_3766_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3768_){
_start:
{
if (lean_obj_tag(v_x_3768_) == 7)
{
lean_object* v_binderName_3769_; lean_object* v_body_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_binderName_3769_ = lean_ctor_get(v_x_3768_, 0);
v_body_3770_ = lean_ctor_get(v_x_3768_, 2);
v___x_3771_ = l_Lean_Expr_getForallBinderNames(v_body_3770_);
lean_inc(v_binderName_3769_);
v___x_3772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3772_, 0, v_binderName_3769_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
return v___x_3772_;
}
else
{
lean_object* v___x_3773_; 
v___x_3773_ = lean_box(0);
return v___x_3773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Expr_getForallBinderNames(v_x_3774_);
lean_dec_ref(v_x_3774_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3776_){
_start:
{
switch(lean_obj_tag(v_x_3776_))
{
case 10:
{
lean_object* v_expr_3777_; 
v_expr_3777_ = lean_ctor_get(v_x_3776_, 1);
v_x_3776_ = v_expr_3777_;
goto _start;
}
case 7:
{
lean_object* v_body_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v_body_3779_ = lean_ctor_get(v_x_3776_, 2);
v___x_3780_ = l_Lean_Expr_getNumHeadForalls(v_body_3779_);
v___x_3781_ = lean_unsigned_to_nat(1u);
v___x_3782_ = lean_nat_add(v___x_3780_, v___x_3781_);
lean_dec(v___x_3780_);
return v___x_3782_;
}
default: 
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_unsigned_to_nat(0u);
return v___x_3783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_Expr_getNumHeadForalls(v_x_3784_);
lean_dec_ref(v_x_3784_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3786_){
_start:
{
if (lean_obj_tag(v_x_3786_) == 5)
{
lean_object* v_fn_3787_; 
v_fn_3787_ = lean_ctor_get(v_x_3786_, 0);
v_x_3786_ = v_fn_3787_;
goto _start;
}
else
{
lean_inc_ref(v_x_3786_);
return v_x_3786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_Expr_getAppFn(v_x_3789_);
lean_dec_ref(v_x_3789_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3791_){
_start:
{
switch(lean_obj_tag(v_x_3791_))
{
case 5:
{
lean_object* v_fn_3792_; 
v_fn_3792_ = lean_ctor_get(v_x_3791_, 0);
v_x_3791_ = v_fn_3792_;
goto _start;
}
case 10:
{
lean_object* v_expr_3794_; 
v_expr_3794_ = lean_ctor_get(v_x_3791_, 1);
v_x_3791_ = v_expr_3794_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3791_);
return v_x_3791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Lean_Expr_getAppFn_x27(v_x_3796_);
lean_dec_ref(v_x_3796_);
return v_res_3797_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3798_, lean_object* v_n_3799_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Lean_Expr_getAppFn(v_e_3798_);
if (lean_obj_tag(v___x_3800_) == 4)
{
lean_object* v_declName_3801_; uint8_t v___x_3802_; 
v_declName_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_declName_3801_);
lean_dec_ref_known(v___x_3800_, 2);
v___x_3802_ = lean_name_eq(v_declName_3801_, v_n_3799_);
lean_dec(v_declName_3801_);
return v___x_3802_;
}
else
{
uint8_t v___x_3803_; 
lean_dec_ref(v___x_3800_);
v___x_3803_ = 0;
return v___x_3803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3804_, lean_object* v_n_3805_){
_start:
{
uint8_t v_res_3806_; lean_object* v_r_3807_; 
v_res_3806_ = l_Lean_Expr_isAppOf(v_e_3804_, v_n_3805_);
lean_dec(v_n_3805_);
lean_dec_ref(v_e_3804_);
v_r_3807_ = lean_box(v_res_3806_);
return v_r_3807_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3808_, lean_object* v_x_3809_, lean_object* v_x_3810_){
_start:
{
switch(lean_obj_tag(v_x_3808_))
{
case 4:
{
lean_object* v_declName_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
v_declName_3811_ = lean_ctor_get(v_x_3808_, 0);
v___x_3812_ = lean_unsigned_to_nat(0u);
v___x_3813_ = lean_nat_dec_eq(v_x_3810_, v___x_3812_);
lean_dec(v_x_3810_);
if (v___x_3813_ == 0)
{
return v___x_3813_;
}
else
{
uint8_t v___x_3814_; 
v___x_3814_ = lean_name_eq(v_declName_3811_, v_x_3809_);
return v___x_3814_;
}
}
case 5:
{
lean_object* v_fn_3815_; lean_object* v_zero_3816_; uint8_t v_isZero_3817_; 
v_fn_3815_ = lean_ctor_get(v_x_3808_, 0);
v_zero_3816_ = lean_unsigned_to_nat(0u);
v_isZero_3817_ = lean_nat_dec_eq(v_x_3810_, v_zero_3816_);
if (v_isZero_3817_ == 0)
{
lean_object* v_one_3818_; lean_object* v_n_3819_; 
v_one_3818_ = lean_unsigned_to_nat(1u);
v_n_3819_ = lean_nat_sub(v_x_3810_, v_one_3818_);
lean_dec(v_x_3810_);
v_x_3808_ = v_fn_3815_;
v_x_3810_ = v_n_3819_;
goto _start;
}
else
{
uint8_t v___x_3821_; 
lean_dec(v_x_3810_);
v___x_3821_ = 0;
return v___x_3821_;
}
}
default: 
{
uint8_t v___x_3822_; 
lean_dec(v_x_3810_);
v___x_3822_ = 0;
return v___x_3822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3823_, lean_object* v_x_3824_, lean_object* v_x_3825_){
_start:
{
uint8_t v_res_3826_; lean_object* v_r_3827_; 
v_res_3826_ = l_Lean_Expr_isAppOfArity(v_x_3823_, v_x_3824_, v_x_3825_);
lean_dec(v_x_3824_);
lean_dec_ref(v_x_3823_);
v_r_3827_ = lean_box(v_res_3826_);
return v_r_3827_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3828_, lean_object* v_x_3829_, lean_object* v_x_3830_){
_start:
{
switch(lean_obj_tag(v_x_3828_))
{
case 10:
{
lean_object* v_expr_3831_; 
v_expr_3831_ = lean_ctor_get(v_x_3828_, 1);
v_x_3828_ = v_expr_3831_;
goto _start;
}
case 4:
{
lean_object* v_declName_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v_declName_3833_ = lean_ctor_get(v_x_3828_, 0);
v___x_3834_ = lean_unsigned_to_nat(0u);
v___x_3835_ = lean_nat_dec_eq(v_x_3830_, v___x_3834_);
lean_dec(v_x_3830_);
if (v___x_3835_ == 0)
{
return v___x_3835_;
}
else
{
uint8_t v___x_3836_; 
v___x_3836_ = lean_name_eq(v_declName_3833_, v_x_3829_);
return v___x_3836_;
}
}
case 5:
{
lean_object* v_fn_3837_; lean_object* v_zero_3838_; uint8_t v_isZero_3839_; 
v_fn_3837_ = lean_ctor_get(v_x_3828_, 0);
v_zero_3838_ = lean_unsigned_to_nat(0u);
v_isZero_3839_ = lean_nat_dec_eq(v_x_3830_, v_zero_3838_);
if (v_isZero_3839_ == 0)
{
lean_object* v_one_3840_; lean_object* v_n_3841_; 
v_one_3840_ = lean_unsigned_to_nat(1u);
v_n_3841_ = lean_nat_sub(v_x_3830_, v_one_3840_);
lean_dec(v_x_3830_);
v_x_3828_ = v_fn_3837_;
v_x_3830_ = v_n_3841_;
goto _start;
}
else
{
uint8_t v___x_3843_; 
lean_dec(v_x_3830_);
v___x_3843_ = 0;
return v___x_3843_;
}
}
default: 
{
uint8_t v___x_3844_; 
lean_dec(v_x_3830_);
v___x_3844_ = 0;
return v___x_3844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3845_, lean_object* v_x_3846_, lean_object* v_x_3847_){
_start:
{
uint8_t v_res_3848_; lean_object* v_r_3849_; 
v_res_3848_ = l_Lean_Expr_isAppOfArity_x27(v_x_3845_, v_x_3846_, v_x_3847_);
lean_dec(v_x_3846_);
lean_dec_ref(v_x_3845_);
v_r_3849_ = lean_box(v_res_3848_);
return v_r_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3850_, lean_object* v_x_3851_){
_start:
{
if (lean_obj_tag(v_x_3850_) == 5)
{
lean_object* v_fn_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v_fn_3852_ = lean_ctor_get(v_x_3850_, 0);
v___x_3853_ = lean_unsigned_to_nat(1u);
v___x_3854_ = lean_nat_add(v_x_3851_, v___x_3853_);
lean_dec(v_x_3851_);
v_x_3850_ = v_fn_3852_;
v_x_3851_ = v___x_3854_;
goto _start;
}
else
{
return v_x_3851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3856_, lean_object* v_x_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3856_, v_x_3857_);
lean_dec_ref(v_x_3856_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3859_){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_unsigned_to_nat(0u);
v___x_3861_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3859_, v___x_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Expr_getAppNumArgs(v_e_3862_);
lean_dec_ref(v_e_3862_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
switch(lean_obj_tag(v_a_3864_))
{
case 10:
{
lean_object* v_expr_3866_; 
v_expr_3866_ = lean_ctor_get(v_a_3864_, 1);
v_a_3864_ = v_expr_3866_;
goto _start;
}
case 5:
{
lean_object* v_fn_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v_fn_3868_ = lean_ctor_get(v_a_3864_, 0);
v___x_3869_ = lean_unsigned_to_nat(1u);
v___x_3870_ = lean_nat_add(v_a_3865_, v___x_3869_);
lean_dec(v_a_3865_);
v_a_3864_ = v_fn_3868_;
v_a_3865_ = v___x_3870_;
goto _start;
}
default: 
{
return v_a_3865_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3872_, v_a_3873_);
lean_dec_ref(v_a_3872_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3875_){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = lean_unsigned_to_nat(0u);
v___x_3877_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3875_, v___x_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3878_);
lean_dec_ref(v_e_3878_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3880_, lean_object* v_x_3881_){
_start:
{
lean_object* v_zero_3882_; uint8_t v_isZero_3883_; 
v_zero_3882_ = lean_unsigned_to_nat(0u);
v_isZero_3883_ = lean_nat_dec_eq(v_x_3880_, v_zero_3882_);
if (v_isZero_3883_ == 0)
{
if (lean_obj_tag(v_x_3881_) == 5)
{
lean_object* v_fn_3884_; lean_object* v_one_3885_; lean_object* v_n_3886_; 
v_fn_3884_ = lean_ctor_get(v_x_3881_, 0);
v_one_3885_ = lean_unsigned_to_nat(1u);
v_n_3886_ = lean_nat_sub(v_x_3880_, v_one_3885_);
lean_dec(v_x_3880_);
v_x_3880_ = v_n_3886_;
v_x_3881_ = v_fn_3884_;
goto _start;
}
else
{
lean_dec(v_x_3880_);
lean_inc_ref(v_x_3881_);
return v_x_3881_;
}
}
else
{
lean_dec(v_x_3880_);
lean_inc_ref(v_x_3881_);
return v_x_3881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3888_, lean_object* v_x_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_Expr_getBoundedAppFn(v_x_3888_, v_x_3889_);
lean_dec_ref(v_x_3889_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3891_, lean_object* v_x_3892_, lean_object* v_x_3893_){
_start:
{
if (lean_obj_tag(v_x_3891_) == 5)
{
lean_object* v_fn_3894_; lean_object* v_arg_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v_fn_3894_ = lean_ctor_get(v_x_3891_, 0);
lean_inc_ref(v_fn_3894_);
v_arg_3895_ = lean_ctor_get(v_x_3891_, 1);
lean_inc_ref(v_arg_3895_);
lean_dec_ref_known(v_x_3891_, 2);
v___x_3896_ = lean_array_set(v_x_3892_, v_x_3893_, v_arg_3895_);
v___x_3897_ = lean_unsigned_to_nat(1u);
v___x_3898_ = lean_nat_sub(v_x_3893_, v___x_3897_);
lean_dec(v_x_3893_);
v_x_3891_ = v_fn_3894_;
v_x_3892_ = v___x_3896_;
v_x_3893_ = v___x_3898_;
goto _start;
}
else
{
lean_dec(v_x_3893_);
lean_dec_ref(v_x_3891_);
return v_x_3892_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3900_; lean_object* v_dummy_3901_; 
v___x_3900_ = lean_box(0);
v_dummy_3901_ = l_Lean_Expr_sort___override(v___x_3900_);
return v_dummy_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3902_){
_start:
{
lean_object* v_dummy_3903_; lean_object* v_nargs_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v_dummy_3903_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3904_ = l_Lean_Expr_getAppNumArgs(v_e_3902_);
lean_inc(v_nargs_3904_);
v___x_3905_ = lean_mk_array(v_nargs_3904_, v_dummy_3903_);
v___x_3906_ = lean_unsigned_to_nat(1u);
v___x_3907_ = lean_nat_sub(v_nargs_3904_, v___x_3906_);
lean_dec(v_nargs_3904_);
v___x_3908_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3902_, v___x_3905_, v___x_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3909_, lean_object* v_x_3910_, lean_object* v_x_3911_){
_start:
{
if (lean_obj_tag(v_x_3909_) == 5)
{
lean_object* v_fn_3912_; lean_object* v_arg_3913_; lean_object* v_zero_3914_; uint8_t v_isZero_3915_; 
v_fn_3912_ = lean_ctor_get(v_x_3909_, 0);
lean_inc_ref(v_fn_3912_);
v_arg_3913_ = lean_ctor_get(v_x_3909_, 1);
lean_inc_ref(v_arg_3913_);
lean_dec_ref_known(v_x_3909_, 2);
v_zero_3914_ = lean_unsigned_to_nat(0u);
v_isZero_3915_ = lean_nat_dec_eq(v_x_3911_, v_zero_3914_);
if (v_isZero_3915_ == 0)
{
lean_object* v_one_3916_; lean_object* v_n_3917_; lean_object* v___x_3918_; 
v_one_3916_ = lean_unsigned_to_nat(1u);
v_n_3917_ = lean_nat_sub(v_x_3911_, v_one_3916_);
lean_dec(v_x_3911_);
v___x_3918_ = lean_array_set(v_x_3910_, v_n_3917_, v_arg_3913_);
v_x_3909_ = v_fn_3912_;
v_x_3910_ = v___x_3918_;
v_x_3911_ = v_n_3917_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3913_);
lean_dec_ref(v_fn_3912_);
lean_dec(v_x_3911_);
return v_x_3910_;
}
}
else
{
lean_dec(v_x_3911_);
lean_dec_ref(v_x_3909_);
return v_x_3910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3920_, lean_object* v_e_3921_){
_start:
{
lean_object* v_dummy_3922_; lean_object* v___y_3924_; lean_object* v___x_3927_; uint8_t v___x_3928_; 
v_dummy_3922_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3927_ = l_Lean_Expr_getAppNumArgs(v_e_3921_);
v___x_3928_ = lean_nat_dec_le(v_maxArgs_3920_, v___x_3927_);
if (v___x_3928_ == 0)
{
lean_dec(v_maxArgs_3920_);
v___y_3924_ = v___x_3927_;
goto v___jp_3923_;
}
else
{
lean_dec(v___x_3927_);
v___y_3924_ = v_maxArgs_3920_;
goto v___jp_3923_;
}
v___jp_3923_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
lean_inc(v___y_3924_);
v___x_3925_ = lean_mk_array(v___y_3924_, v_dummy_3922_);
v___x_3926_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3921_, v___x_3925_, v___y_3924_);
return v___x_3926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3929_, lean_object* v_x_3930_){
_start:
{
if (lean_obj_tag(v_x_3929_) == 5)
{
lean_object* v_fn_3931_; lean_object* v_arg_3932_; lean_object* v___x_3933_; 
v_fn_3931_ = lean_ctor_get(v_x_3929_, 0);
lean_inc_ref(v_fn_3931_);
v_arg_3932_ = lean_ctor_get(v_x_3929_, 1);
lean_inc_ref(v_arg_3932_);
lean_dec_ref_known(v_x_3929_, 2);
v___x_3933_ = lean_array_push(v_x_3930_, v_arg_3932_);
v_x_3929_ = v_fn_3931_;
v_x_3930_ = v___x_3933_;
goto _start;
}
else
{
lean_dec_ref(v_x_3929_);
return v_x_3930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3935_){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3936_ = l_Lean_Expr_getAppNumArgs(v_e_3935_);
v___x_3937_ = lean_mk_empty_array_with_capacity(v___x_3936_);
lean_dec(v___x_3936_);
v___x_3938_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3935_, v___x_3937_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3939_, lean_object* v_x_3940_, lean_object* v_x_3941_, lean_object* v_x_3942_){
_start:
{
if (lean_obj_tag(v_x_3940_) == 5)
{
lean_object* v_fn_3943_; lean_object* v_arg_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v_fn_3943_ = lean_ctor_get(v_x_3940_, 0);
lean_inc_ref(v_fn_3943_);
v_arg_3944_ = lean_ctor_get(v_x_3940_, 1);
lean_inc_ref(v_arg_3944_);
lean_dec_ref_known(v_x_3940_, 2);
v___x_3945_ = lean_array_set(v_x_3941_, v_x_3942_, v_arg_3944_);
v___x_3946_ = lean_unsigned_to_nat(1u);
v___x_3947_ = lean_nat_sub(v_x_3942_, v___x_3946_);
lean_dec(v_x_3942_);
v_x_3940_ = v_fn_3943_;
v_x_3941_ = v___x_3945_;
v_x_3942_ = v___x_3947_;
goto _start;
}
else
{
lean_object* v___x_3949_; 
lean_dec(v_x_3942_);
v___x_3949_ = lean_apply_2(v_k_3939_, v_x_3940_, v_x_3941_);
return v___x_3949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3950_, lean_object* v_k_3951_, lean_object* v_x_3952_, lean_object* v_x_3953_, lean_object* v_x_3954_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l_Lean_Expr_withAppAux___redArg(v_k_3951_, v_x_3952_, v_x_3953_, v_x_3954_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3956_, lean_object* v_k_3957_){
_start:
{
lean_object* v_dummy_3958_; lean_object* v_nargs_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_dummy_3958_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3959_ = l_Lean_Expr_getAppNumArgs(v_e_3956_);
lean_inc(v_nargs_3959_);
v___x_3960_ = lean_mk_array(v_nargs_3959_, v_dummy_3958_);
v___x_3961_ = lean_unsigned_to_nat(1u);
v___x_3962_ = lean_nat_sub(v_nargs_3959_, v___x_3961_);
lean_dec(v_nargs_3959_);
v___x_3963_ = l_Lean_Expr_withAppAux___redArg(v_k_3957_, v_e_3956_, v___x_3960_, v___x_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3964_, lean_object* v_e_3965_, lean_object* v_k_3966_){
_start:
{
lean_object* v_dummy_3967_; lean_object* v_nargs_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v_dummy_3967_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3968_ = l_Lean_Expr_getAppNumArgs(v_e_3965_);
lean_inc(v_nargs_3968_);
v___x_3969_ = lean_mk_array(v_nargs_3968_, v_dummy_3967_);
v___x_3970_ = lean_unsigned_to_nat(1u);
v___x_3971_ = lean_nat_sub(v_nargs_3968_, v___x_3970_);
lean_dec(v_nargs_3968_);
v___x_3972_ = l_Lean_Expr_withAppAux___redArg(v_k_3966_, v_e_3965_, v___x_3969_, v___x_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3973_, lean_object* v_x_3974_, lean_object* v_x_3975_){
_start:
{
if (lean_obj_tag(v_x_3973_) == 5)
{
lean_object* v_fn_3976_; lean_object* v_arg_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v_fn_3976_ = lean_ctor_get(v_x_3973_, 0);
lean_inc_ref(v_fn_3976_);
v_arg_3977_ = lean_ctor_get(v_x_3973_, 1);
lean_inc_ref(v_arg_3977_);
lean_dec_ref_known(v_x_3973_, 2);
v___x_3978_ = lean_array_set(v_x_3974_, v_x_3975_, v_arg_3977_);
v___x_3979_ = lean_unsigned_to_nat(1u);
v___x_3980_ = lean_nat_sub(v_x_3975_, v___x_3979_);
lean_dec(v_x_3975_);
v_x_3973_ = v_fn_3976_;
v_x_3974_ = v___x_3978_;
v_x_3975_ = v___x_3980_;
goto _start;
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
lean_dec(v_x_3975_);
v___x_3982_ = l_Lean_Expr_constName(v_x_3973_);
lean_dec_ref(v_x_3973_);
v___x_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3982_);
lean_ctor_set(v___x_3983_, 1, v_x_3974_);
return v___x_3983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3984_){
_start:
{
lean_object* v_dummy_3985_; lean_object* v_nargs_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_dummy_3985_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3986_ = l_Lean_Expr_getAppNumArgs(v_e_3984_);
lean_inc(v_nargs_3986_);
v___x_3987_ = lean_mk_array(v_nargs_3986_, v_dummy_3985_);
v___x_3988_ = lean_unsigned_to_nat(1u);
v___x_3989_ = lean_nat_sub(v_nargs_3986_, v___x_3988_);
lean_dec(v_nargs_3986_);
v___x_3990_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3984_, v___x_3987_, v___x_3989_);
return v___x_3990_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Array_instInhabited___redArg();
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_3992_){
_start:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3993_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_3994_ = lean_panic_fn_borrowed(v___x_3993_, v_msg_3992_);
return v___x_3994_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_3997_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_3998_ = lean_unsigned_to_nat(27u);
v___x_3999_ = lean_unsigned_to_nat(1289u);
v___x_4000_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_4001_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4002_ = l_mkPanicMessageWithDecl(v___x_4001_, v___x_4000_, v___x_3999_, v___x_3998_, v___x_3997_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_){
_start:
{
lean_object* v_zero_4006_; uint8_t v_isZero_4007_; 
v_zero_4006_ = lean_unsigned_to_nat(0u);
v_isZero_4007_ = lean_nat_dec_eq(v_a_4003_, v_zero_4006_);
if (v_isZero_4007_ == 1)
{
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
return v_a_4005_;
}
else
{
if (lean_obj_tag(v_a_4004_) == 5)
{
lean_object* v_fn_4008_; lean_object* v_arg_4009_; lean_object* v_one_4010_; lean_object* v_n_4011_; lean_object* v___x_4012_; 
v_fn_4008_ = lean_ctor_get(v_a_4004_, 0);
lean_inc_ref(v_fn_4008_);
v_arg_4009_ = lean_ctor_get(v_a_4004_, 1);
lean_inc_ref(v_arg_4009_);
lean_dec_ref_known(v_a_4004_, 2);
v_one_4010_ = lean_unsigned_to_nat(1u);
v_n_4011_ = lean_nat_sub(v_a_4003_, v_one_4010_);
lean_dec(v_a_4003_);
v___x_4012_ = lean_array_set(v_a_4005_, v_n_4011_, v_arg_4009_);
v_a_4003_ = v_n_4011_;
v_a_4004_ = v_fn_4008_;
v_a_4005_ = v___x_4012_;
goto _start;
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_dec_ref(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
v___x_4014_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4015_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4014_);
return v___x_4015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4016_, lean_object* v_n_4017_){
_start:
{
lean_object* v_dummy_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v_dummy_4018_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4017_);
v___x_4019_ = lean_mk_array(v_n_4017_, v_dummy_4018_);
v___x_4020_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4017_, v_e_4016_, v___x_4019_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4021_, lean_object* v_n_4022_){
_start:
{
lean_object* v_zero_4023_; uint8_t v_isZero_4024_; 
v_zero_4023_ = lean_unsigned_to_nat(0u);
v_isZero_4024_ = lean_nat_dec_eq(v_n_4022_, v_zero_4023_);
if (v_isZero_4024_ == 1)
{
lean_dec(v_n_4022_);
lean_inc_ref(v_e_4021_);
return v_e_4021_;
}
else
{
if (lean_obj_tag(v_e_4021_) == 5)
{
lean_object* v_fn_4025_; lean_object* v_one_4026_; lean_object* v_n_4027_; 
v_fn_4025_ = lean_ctor_get(v_e_4021_, 0);
v_one_4026_ = lean_unsigned_to_nat(1u);
v_n_4027_ = lean_nat_sub(v_n_4022_, v_one_4026_);
lean_dec(v_n_4022_);
v_e_4021_ = v_fn_4025_;
v_n_4022_ = v_n_4027_;
goto _start;
}
else
{
lean_dec(v_n_4022_);
lean_inc_ref(v_e_4021_);
return v_e_4021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4029_, lean_object* v_n_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Lean_Expr_stripArgsN(v_e_4029_, v_n_4030_);
lean_dec_ref(v_e_4029_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4032_, lean_object* v_n_4033_){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4034_ = l_Lean_Expr_getAppNumArgs(v_e_4032_);
v___x_4035_ = lean_nat_sub(v___x_4034_, v_n_4033_);
lean_dec(v___x_4034_);
v___x_4036_ = l_Lean_Expr_stripArgsN(v_e_4032_, v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4037_, lean_object* v_n_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_Expr_getAppPrefix(v_e_4037_, v_n_4038_);
lean_dec(v_n_4038_);
lean_dec_ref(v_e_4037_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4040_, lean_object* v_inst_4041_, lean_object* v_f_4042_, lean_object* v_x_4043_){
_start:
{
size_t v_sz_4044_; size_t v___x_4045_; lean_object* v___x_4046_; 
v_sz_4044_ = lean_array_size(v_args_4040_);
v___x_4045_ = ((size_t)0ULL);
v___x_4046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4041_, v_f_4042_, v_sz_4044_, v___x_4045_, v_args_4040_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4048_, lean_object* v_inst_4049_, lean_object* v_f_4050_, lean_object* v_toSeq_4051_, lean_object* v_fn_4052_, lean_object* v_args_4053_){
_start:
{
lean_object* v_map_4054_; lean_object* v___f_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v_map_4054_ = lean_ctor_get(v_toFunctor_4048_, 0);
lean_inc(v_map_4054_);
lean_dec_ref(v_toFunctor_4048_);
lean_inc(v_f_4050_);
v___f_4055_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4055_, 0, v_args_4053_);
lean_closure_set(v___f_4055_, 1, v_inst_4049_);
lean_closure_set(v___f_4055_, 2, v_f_4050_);
v___x_4056_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4057_ = lean_apply_1(v_f_4050_, v_fn_4052_);
v___x_4058_ = lean_apply_4(v_map_4054_, lean_box(0), lean_box(0), v___x_4056_, v___x_4057_);
v___x_4059_ = lean_apply_4(v_toSeq_4051_, lean_box(0), lean_box(0), v___x_4058_, v___f_4055_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4060_, lean_object* v_f_4061_, lean_object* v_e_4062_){
_start:
{
lean_object* v_toApplicative_4063_; lean_object* v_toFunctor_4064_; lean_object* v_toSeq_4065_; lean_object* v___f_4066_; lean_object* v_dummy_4067_; lean_object* v_nargs_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v_toApplicative_4063_ = lean_ctor_get(v_inst_4060_, 0);
v_toFunctor_4064_ = lean_ctor_get(v_toApplicative_4063_, 0);
lean_inc_ref(v_toFunctor_4064_);
v_toSeq_4065_ = lean_ctor_get(v_toApplicative_4063_, 2);
lean_inc(v_toSeq_4065_);
v___f_4066_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4066_, 0, v_toFunctor_4064_);
lean_closure_set(v___f_4066_, 1, v_inst_4060_);
lean_closure_set(v___f_4066_, 2, v_f_4061_);
lean_closure_set(v___f_4066_, 3, v_toSeq_4065_);
v_dummy_4067_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4068_ = l_Lean_Expr_getAppNumArgs(v_e_4062_);
lean_inc(v_nargs_4068_);
v___x_4069_ = lean_mk_array(v_nargs_4068_, v_dummy_4067_);
v___x_4070_ = lean_unsigned_to_nat(1u);
v___x_4071_ = lean_nat_sub(v_nargs_4068_, v___x_4070_);
lean_dec(v_nargs_4068_);
v___x_4072_ = l_Lean_Expr_withAppAux___redArg(v___f_4066_, v_e_4062_, v___x_4069_, v___x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4073_, lean_object* v_inst_4074_, lean_object* v_f_4075_, lean_object* v_e_4076_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Lean_Expr_traverseApp___redArg(v_inst_4074_, v_f_4075_, v_e_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4078_, lean_object* v_x_4079_, lean_object* v_x_4080_){
_start:
{
if (lean_obj_tag(v_x_4079_) == 5)
{
lean_object* v_fn_4081_; lean_object* v_arg_4082_; lean_object* v___x_4083_; 
v_fn_4081_ = lean_ctor_get(v_x_4079_, 0);
lean_inc_ref(v_fn_4081_);
v_arg_4082_ = lean_ctor_get(v_x_4079_, 1);
lean_inc_ref(v_arg_4082_);
lean_dec_ref_known(v_x_4079_, 2);
v___x_4083_ = lean_array_push(v_x_4080_, v_arg_4082_);
v_x_4079_ = v_fn_4081_;
v_x_4080_ = v___x_4083_;
goto _start;
}
else
{
lean_object* v___x_4085_; 
v___x_4085_ = lean_apply_2(v_k_4078_, v_x_4079_, v_x_4080_);
return v___x_4085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4086_, lean_object* v_k_4087_, lean_object* v_x_4088_, lean_object* v_x_4089_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4087_, v_x_4088_, v_x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4091_, lean_object* v_k_4092_){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4093_ = l_Lean_Expr_getAppNumArgs(v_e_4091_);
v___x_4094_ = lean_mk_empty_array_with_capacity(v___x_4093_);
lean_dec(v___x_4093_);
v___x_4095_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4092_, v_e_4091_, v___x_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4096_, lean_object* v_e_4097_, lean_object* v_k_4098_){
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
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4102_, lean_object* v_x_4103_, lean_object* v_x_4104_){
_start:
{
if (lean_obj_tag(v_x_4102_) == 5)
{
lean_object* v_fn_4105_; lean_object* v_arg_4106_; lean_object* v_zero_4107_; uint8_t v_isZero_4108_; 
v_fn_4105_ = lean_ctor_get(v_x_4102_, 0);
v_arg_4106_ = lean_ctor_get(v_x_4102_, 1);
v_zero_4107_ = lean_unsigned_to_nat(0u);
v_isZero_4108_ = lean_nat_dec_eq(v_x_4103_, v_zero_4107_);
if (v_isZero_4108_ == 1)
{
lean_dec(v_x_4103_);
lean_inc_ref(v_arg_4106_);
return v_arg_4106_;
}
else
{
lean_object* v_one_4109_; lean_object* v_n_4110_; 
v_one_4109_ = lean_unsigned_to_nat(1u);
v_n_4110_ = lean_nat_sub(v_x_4103_, v_one_4109_);
lean_dec(v_x_4103_);
v_x_4102_ = v_fn_4105_;
v_x_4103_ = v_n_4110_;
goto _start;
}
}
else
{
lean_dec(v_x_4103_);
lean_inc_ref(v_x_4104_);
return v_x_4104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4112_, lean_object* v_x_4113_, lean_object* v_x_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Lean_Expr_getRevArgD(v_x_4112_, v_x_4113_, v_x_4114_);
lean_dec_ref(v_x_4114_);
lean_dec_ref(v_x_4112_);
return v_res_4115_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4118_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4119_ = lean_unsigned_to_nat(20u);
v___x_4120_ = lean_unsigned_to_nat(1330u);
v___x_4121_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4122_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4123_ = l_mkPanicMessageWithDecl(v___x_4122_, v___x_4121_, v___x_4120_, v___x_4119_, v___x_4118_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4124_, lean_object* v_x_4125_){
_start:
{
if (lean_obj_tag(v_x_4124_) == 5)
{
lean_object* v_fn_4126_; lean_object* v_arg_4127_; lean_object* v_zero_4128_; uint8_t v_isZero_4129_; 
v_fn_4126_ = lean_ctor_get(v_x_4124_, 0);
v_arg_4127_ = lean_ctor_get(v_x_4124_, 1);
v_zero_4128_ = lean_unsigned_to_nat(0u);
v_isZero_4129_ = lean_nat_dec_eq(v_x_4125_, v_zero_4128_);
if (v_isZero_4129_ == 1)
{
lean_dec(v_x_4125_);
lean_inc_ref(v_arg_4127_);
return v_arg_4127_;
}
else
{
lean_object* v_one_4130_; lean_object* v_n_4131_; 
v_one_4130_ = lean_unsigned_to_nat(1u);
v_n_4131_ = lean_nat_sub(v_x_4125_, v_one_4130_);
lean_dec(v_x_4125_);
v_x_4124_ = v_fn_4126_;
v_x_4125_ = v_n_4131_;
goto _start;
}
}
else
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_dec(v_x_4125_);
v___x_4133_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4134_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4133_);
return v___x_4134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4135_, lean_object* v_x_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_Expr_getRevArg_x21(v_x_4135_, v_x_4136_);
lean_dec_ref(v_x_4135_);
return v_res_4137_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4139_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4140_ = lean_unsigned_to_nat(20u);
v___x_4141_ = lean_unsigned_to_nat(1337u);
v___x_4142_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4143_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4144_ = l_mkPanicMessageWithDecl(v___x_4143_, v___x_4142_, v___x_4141_, v___x_4140_, v___x_4139_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4145_, lean_object* v_x_4146_){
_start:
{
switch(lean_obj_tag(v_x_4145_))
{
case 10:
{
lean_object* v_expr_4147_; 
v_expr_4147_ = lean_ctor_get(v_x_4145_, 1);
v_x_4145_ = v_expr_4147_;
goto _start;
}
case 5:
{
lean_object* v_fn_4149_; lean_object* v_arg_4150_; lean_object* v_zero_4151_; uint8_t v_isZero_4152_; 
v_fn_4149_ = lean_ctor_get(v_x_4145_, 0);
v_arg_4150_ = lean_ctor_get(v_x_4145_, 1);
v_zero_4151_ = lean_unsigned_to_nat(0u);
v_isZero_4152_ = lean_nat_dec_eq(v_x_4146_, v_zero_4151_);
if (v_isZero_4152_ == 1)
{
lean_dec(v_x_4146_);
lean_inc_ref(v_arg_4150_);
return v_arg_4150_;
}
else
{
lean_object* v_one_4153_; lean_object* v_n_4154_; 
v_one_4153_ = lean_unsigned_to_nat(1u);
v_n_4154_ = lean_nat_sub(v_x_4146_, v_one_4153_);
lean_dec(v_x_4146_);
v_x_4145_ = v_fn_4149_;
v_x_4146_ = v_n_4154_;
goto _start;
}
}
default: 
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
lean_dec(v_x_4146_);
v___x_4156_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4157_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4156_);
return v___x_4157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4158_, lean_object* v_x_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4158_, v_x_4159_);
lean_dec_ref(v_x_4158_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4161_, lean_object* v_i_4162_, lean_object* v_n_4163_){
_start:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4164_ = lean_nat_sub(v_n_4163_, v_i_4162_);
v___x_4165_ = lean_unsigned_to_nat(1u);
v___x_4166_ = lean_nat_sub(v___x_4164_, v___x_4165_);
lean_dec(v___x_4164_);
v___x_4167_ = l_Lean_Expr_getRevArg_x21(v_e_4161_, v___x_4166_);
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4168_, lean_object* v_i_4169_, lean_object* v_n_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_Expr_getArg_x21(v_e_4168_, v_i_4169_, v_n_4170_);
lean_dec(v_n_4170_);
lean_dec(v_i_4169_);
lean_dec_ref(v_e_4168_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4172_, lean_object* v_i_4173_, lean_object* v_n_4174_){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4175_ = lean_nat_sub(v_n_4174_, v_i_4173_);
v___x_4176_ = lean_unsigned_to_nat(1u);
v___x_4177_ = lean_nat_sub(v___x_4175_, v___x_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4172_, v___x_4177_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4179_, lean_object* v_i_4180_, lean_object* v_n_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Lean_Expr_getArg_x21_x27(v_e_4179_, v_i_4180_, v_n_4181_);
lean_dec(v_n_4181_);
lean_dec(v_i_4180_);
lean_dec_ref(v_e_4179_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4183_, lean_object* v_i_4184_, lean_object* v_v_u2080_4185_, lean_object* v_n_4186_){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4187_ = lean_nat_sub(v_n_4186_, v_i_4184_);
v___x_4188_ = lean_unsigned_to_nat(1u);
v___x_4189_ = lean_nat_sub(v___x_4187_, v___x_4188_);
lean_dec(v___x_4187_);
v___x_4190_ = l_Lean_Expr_getRevArgD(v_e_4183_, v___x_4189_, v_v_u2080_4185_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4191_, lean_object* v_i_4192_, lean_object* v_v_u2080_4193_, lean_object* v_n_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Expr_getArgD(v_e_4191_, v_i_4192_, v_v_u2080_4193_, v_n_4194_);
lean_dec(v_n_4194_);
lean_dec_ref(v_v_u2080_4193_);
lean_dec(v_i_4192_);
lean_dec_ref(v_e_4191_);
return v_res_4195_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4196_){
_start:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; uint8_t v___x_4199_; 
v___x_4197_ = lean_unsigned_to_nat(0u);
v___x_4198_ = l_Lean_Expr_looseBVarRange(v_e_4196_);
v___x_4199_ = lean_nat_dec_lt(v___x_4197_, v___x_4198_);
lean_dec(v___x_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4200_){
_start:
{
uint8_t v_res_4201_; lean_object* v_r_4202_; 
v_res_4201_ = l_Lean_Expr_hasLooseBVars(v_e_4200_);
lean_dec_ref(v_e_4200_);
v_r_4202_ = lean_box(v_res_4201_);
return v_r_4202_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4203_){
_start:
{
if (lean_obj_tag(v_e_4203_) == 7)
{
lean_object* v_body_4204_; uint8_t v___x_4205_; 
v_body_4204_ = lean_ctor_get(v_e_4203_, 2);
v___x_4205_ = l_Lean_Expr_hasLooseBVars(v_body_4204_);
if (v___x_4205_ == 0)
{
uint8_t v___x_4206_; 
v___x_4206_ = 1;
return v___x_4206_;
}
else
{
uint8_t v___x_4207_; 
v___x_4207_ = 0;
return v___x_4207_;
}
}
else
{
uint8_t v___x_4208_; 
v___x_4208_ = 0;
return v___x_4208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4209_){
_start:
{
uint8_t v_res_4210_; lean_object* v_r_4211_; 
v_res_4210_ = l_Lean_Expr_isArrow(v_e_4209_);
lean_dec_ref(v_e_4209_);
v_r_4211_ = lean_box(v_res_4210_);
return v_r_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4214_, lean_object* v_bvarIdx_4215_){
_start:
{
uint8_t v_res_4216_; lean_object* v_r_4217_; 
v_res_4216_ = lean_expr_has_loose_bvar(v_e_4214_, v_bvarIdx_4215_);
lean_dec(v_bvarIdx_4215_);
lean_dec_ref(v_e_4214_);
v_r_4217_ = lean_box(v_res_4216_);
return v_r_4217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4218_, lean_object* v_bvarIdx_4219_, uint8_t v_considerRange_4220_){
_start:
{
if (lean_obj_tag(v_e_4218_) == 7)
{
lean_object* v_binderType_4221_; lean_object* v_body_4222_; uint8_t v_binderInfo_4223_; uint8_t v___x_4228_; 
v_binderType_4221_ = lean_ctor_get(v_e_4218_, 1);
v_body_4222_ = lean_ctor_get(v_e_4218_, 2);
v_binderInfo_4223_ = lean_ctor_get_uint8(v_e_4218_, sizeof(void*)*3 + 8);
v___x_4228_ = lean_expr_has_loose_bvar(v_binderType_4221_, v_bvarIdx_4219_);
if (v___x_4228_ == 0)
{
goto v___jp_4224_;
}
else
{
uint8_t v___x_4229_; 
v___x_4229_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4223_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; uint8_t v___x_4231_; 
v___x_4230_ = lean_unsigned_to_nat(0u);
v___x_4231_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4222_, v___x_4230_, v_considerRange_4220_);
if (v___x_4231_ == 0)
{
goto v___jp_4224_;
}
else
{
lean_dec(v_bvarIdx_4219_);
return v___x_4231_;
}
}
else
{
lean_dec(v_bvarIdx_4219_);
return v___x_4229_;
}
}
v___jp_4224_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = lean_unsigned_to_nat(1u);
v___x_4226_ = lean_nat_add(v_bvarIdx_4219_, v___x_4225_);
lean_dec(v_bvarIdx_4219_);
v_e_4218_ = v_body_4222_;
v_bvarIdx_4219_ = v___x_4226_;
goto _start;
}
}
else
{
if (v_considerRange_4220_ == 0)
{
lean_dec(v_bvarIdx_4219_);
return v_considerRange_4220_;
}
else
{
uint8_t v___x_4232_; 
v___x_4232_ = lean_expr_has_loose_bvar(v_e_4218_, v_bvarIdx_4219_);
lean_dec(v_bvarIdx_4219_);
return v___x_4232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4233_, lean_object* v_bvarIdx_4234_, lean_object* v_considerRange_4235_){
_start:
{
uint8_t v_considerRange_boxed_4236_; uint8_t v_res_4237_; lean_object* v_r_4238_; 
v_considerRange_boxed_4236_ = lean_unbox(v_considerRange_4235_);
v_res_4237_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4233_, v_bvarIdx_4234_, v_considerRange_boxed_4236_);
lean_dec_ref(v_e_4233_);
v_r_4238_ = lean_box(v_res_4237_);
return v_r_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4242_, lean_object* v_s_4243_, lean_object* v_d_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = lean_expr_lower_loose_bvars(v_e_4242_, v_s_4243_, v_d_4244_);
lean_dec(v_d_4244_);
lean_dec(v_s_4243_);
lean_dec_ref(v_e_4242_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4249_, lean_object* v_s_4250_, lean_object* v_d_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = lean_expr_lift_loose_bvars(v_e_4249_, v_s_4250_, v_d_4251_);
lean_dec(v_d_4251_);
lean_dec(v_s_4250_);
lean_dec_ref(v_e_4249_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4253_, lean_object* v_numParams_4254_, uint8_t v_considerRange_4255_){
_start:
{
if (lean_obj_tag(v_e_4253_) == 7)
{
lean_object* v_binderName_4256_; lean_object* v_binderType_4257_; lean_object* v_body_4258_; uint8_t v_binderInfo_4259_; lean_object* v_zero_4260_; uint8_t v_isZero_4261_; 
v_binderName_4256_ = lean_ctor_get(v_e_4253_, 0);
v_binderType_4257_ = lean_ctor_get(v_e_4253_, 1);
v_body_4258_ = lean_ctor_get(v_e_4253_, 2);
v_binderInfo_4259_ = lean_ctor_get_uint8(v_e_4253_, sizeof(void*)*3 + 8);
v_zero_4260_ = lean_unsigned_to_nat(0u);
v_isZero_4261_ = lean_nat_dec_eq(v_numParams_4254_, v_zero_4260_);
if (v_isZero_4261_ == 0)
{
lean_object* v_one_4262_; lean_object* v_n_4263_; lean_object* v_b_4264_; uint8_t v___x_4265_; 
lean_inc_ref(v_body_4258_);
lean_inc_ref(v_binderType_4257_);
lean_inc(v_binderName_4256_);
lean_dec_ref_known(v_e_4253_, 3);
v_one_4262_ = lean_unsigned_to_nat(1u);
v_n_4263_ = lean_nat_sub(v_numParams_4254_, v_one_4262_);
v_b_4264_ = l_Lean_Expr_inferImplicit(v_body_4258_, v_n_4263_, v_considerRange_4255_);
lean_dec(v_n_4263_);
v___x_4265_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4259_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_Expr_forallE___override(v_binderName_4256_, v_binderType_4257_, v_b_4264_, v_binderInfo_4259_);
return v___x_4266_;
}
else
{
uint8_t v___x_4267_; 
v___x_4267_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4264_, v_zero_4260_, v_considerRange_4255_);
if (v___x_4267_ == 0)
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_Expr_forallE___override(v_binderName_4256_, v_binderType_4257_, v_b_4264_, v_binderInfo_4259_);
return v___x_4268_;
}
else
{
uint8_t v___x_4269_; lean_object* v___x_4270_; 
v___x_4269_ = 1;
v___x_4270_ = l_Lean_Expr_forallE___override(v_binderName_4256_, v_binderType_4257_, v_b_4264_, v___x_4269_);
return v___x_4270_;
}
}
}
else
{
return v_e_4253_;
}
}
else
{
return v_e_4253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4271_, lean_object* v_numParams_4272_, lean_object* v_considerRange_4273_){
_start:
{
uint8_t v_considerRange_boxed_4274_; lean_object* v_res_4275_; 
v_considerRange_boxed_4274_ = lean_unbox(v_considerRange_4273_);
v_res_4275_ = l_Lean_Expr_inferImplicit(v_e_4271_, v_numParams_4272_, v_considerRange_boxed_4274_);
lean_dec(v_numParams_4272_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4276_, lean_object* v_binderInfos_x3f_4277_){
_start:
{
if (lean_obj_tag(v_e_4276_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4277_) == 1)
{
lean_object* v_binderName_4278_; lean_object* v_binderType_4279_; lean_object* v_body_4280_; uint8_t v_binderInfo_4281_; lean_object* v_head_4282_; lean_object* v_tail_4283_; lean_object* v_b_4284_; 
v_binderName_4278_ = lean_ctor_get(v_e_4276_, 0);
lean_inc(v_binderName_4278_);
v_binderType_4279_ = lean_ctor_get(v_e_4276_, 1);
lean_inc_ref(v_binderType_4279_);
v_body_4280_ = lean_ctor_get(v_e_4276_, 2);
lean_inc_ref(v_body_4280_);
v_binderInfo_4281_ = lean_ctor_get_uint8(v_e_4276_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4276_, 3);
v_head_4282_ = lean_ctor_get(v_binderInfos_x3f_4277_, 0);
v_tail_4283_ = lean_ctor_get(v_binderInfos_x3f_4277_, 1);
v_b_4284_ = l_Lean_Expr_updateForallBinderInfos(v_body_4280_, v_tail_4283_);
if (lean_obj_tag(v_head_4282_) == 0)
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Lean_Expr_forallE___override(v_binderName_4278_, v_binderType_4279_, v_b_4284_, v_binderInfo_4281_);
return v___x_4285_;
}
else
{
lean_object* v_val_4286_; uint8_t v___x_4287_; lean_object* v___x_4288_; 
v_val_4286_ = lean_ctor_get(v_head_4282_, 0);
v___x_4287_ = lean_unbox(v_val_4286_);
v___x_4288_ = l_Lean_Expr_forallE___override(v_binderName_4278_, v_binderType_4279_, v_b_4284_, v___x_4287_);
return v___x_4288_;
}
}
else
{
return v_e_4276_;
}
}
else
{
return v_e_4276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4289_, lean_object* v_binderInfos_x3f_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_Expr_updateForallBinderInfos(v_e_4289_, v_binderInfos_x3f_4290_);
lean_dec(v_binderInfos_x3f_4290_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4292_, lean_object* v_binderNames_x3f_4293_){
_start:
{
switch(lean_obj_tag(v_e_4292_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4293_) == 1)
{
lean_object* v_binderName_4294_; lean_object* v_binderType_4295_; lean_object* v_body_4296_; uint8_t v_binderInfo_4297_; lean_object* v_head_4298_; lean_object* v_tail_4299_; lean_object* v_b_4300_; 
v_binderName_4294_ = lean_ctor_get(v_e_4292_, 0);
lean_inc(v_binderName_4294_);
v_binderType_4295_ = lean_ctor_get(v_e_4292_, 1);
lean_inc_ref(v_binderType_4295_);
v_body_4296_ = lean_ctor_get(v_e_4292_, 2);
lean_inc_ref(v_body_4296_);
v_binderInfo_4297_ = lean_ctor_get_uint8(v_e_4292_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4292_, 3);
v_head_4298_ = lean_ctor_get(v_binderNames_x3f_4293_, 0);
lean_inc(v_head_4298_);
v_tail_4299_ = lean_ctor_get(v_binderNames_x3f_4293_, 1);
lean_inc(v_tail_4299_);
lean_dec_ref_known(v_binderNames_x3f_4293_, 2);
v_b_4300_ = l_Lean_Expr_updateBinderNames(v_body_4296_, v_tail_4299_);
if (lean_obj_tag(v_head_4298_) == 0)
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Lean_Expr_forallE___override(v_binderName_4294_, v_binderType_4295_, v_b_4300_, v_binderInfo_4297_);
return v___x_4301_;
}
else
{
lean_object* v_val_4302_; lean_object* v___x_4303_; 
lean_dec(v_binderName_4294_);
v_val_4302_ = lean_ctor_get(v_head_4298_, 0);
lean_inc(v_val_4302_);
lean_dec_ref_known(v_head_4298_, 1);
v___x_4303_ = l_Lean_Expr_forallE___override(v_val_4302_, v_binderType_4295_, v_b_4300_, v_binderInfo_4297_);
return v___x_4303_;
}
}
else
{
lean_dec(v_binderNames_x3f_4293_);
return v_e_4292_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4293_) == 1)
{
lean_object* v_binderName_4304_; lean_object* v_binderType_4305_; lean_object* v_body_4306_; uint8_t v_binderInfo_4307_; lean_object* v_head_4308_; lean_object* v_tail_4309_; lean_object* v_b_4310_; 
v_binderName_4304_ = lean_ctor_get(v_e_4292_, 0);
lean_inc(v_binderName_4304_);
v_binderType_4305_ = lean_ctor_get(v_e_4292_, 1);
lean_inc_ref(v_binderType_4305_);
v_body_4306_ = lean_ctor_get(v_e_4292_, 2);
lean_inc_ref(v_body_4306_);
v_binderInfo_4307_ = lean_ctor_get_uint8(v_e_4292_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4292_, 3);
v_head_4308_ = lean_ctor_get(v_binderNames_x3f_4293_, 0);
lean_inc(v_head_4308_);
v_tail_4309_ = lean_ctor_get(v_binderNames_x3f_4293_, 1);
lean_inc(v_tail_4309_);
lean_dec_ref_known(v_binderNames_x3f_4293_, 2);
v_b_4310_ = l_Lean_Expr_updateBinderNames(v_body_4306_, v_tail_4309_);
if (lean_obj_tag(v_head_4308_) == 0)
{
lean_object* v___x_4311_; 
v___x_4311_ = l_Lean_Expr_lam___override(v_binderName_4304_, v_binderType_4305_, v_b_4310_, v_binderInfo_4307_);
return v___x_4311_;
}
else
{
lean_object* v_val_4312_; lean_object* v___x_4313_; 
lean_dec(v_binderName_4304_);
v_val_4312_ = lean_ctor_get(v_head_4308_, 0);
lean_inc(v_val_4312_);
lean_dec_ref_known(v_head_4308_, 1);
v___x_4313_ = l_Lean_Expr_lam___override(v_val_4312_, v_binderType_4305_, v_b_4310_, v_binderInfo_4307_);
return v___x_4313_;
}
}
else
{
lean_dec(v_binderNames_x3f_4293_);
return v_e_4292_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4293_);
return v_e_4292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4316_, lean_object* v_subst_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = lean_expr_instantiate(v_e_4316_, v_subst_4317_);
lean_dec_ref(v_subst_4317_);
lean_dec_ref(v_e_4316_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4321_, lean_object* v_subst_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = lean_expr_instantiate1(v_e_4321_, v_subst_4322_);
lean_dec_ref(v_subst_4322_);
lean_dec_ref(v_e_4321_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4326_, lean_object* v_subst_4327_){
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = lean_expr_instantiate_rev(v_e_4326_, v_subst_4327_);
lean_dec_ref(v_subst_4327_);
lean_dec_ref(v_e_4326_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4333_, lean_object* v_beginIdx_4334_, lean_object* v_endIdx_4335_, lean_object* v_subst_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = lean_expr_instantiate_range(v_e_4333_, v_beginIdx_4334_, v_endIdx_4335_, v_subst_4336_);
lean_dec_ref(v_subst_4336_);
lean_dec(v_endIdx_4335_);
lean_dec(v_beginIdx_4334_);
lean_dec_ref(v_e_4333_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4342_, lean_object* v_beginIdx_4343_, lean_object* v_endIdx_4344_, lean_object* v_subst_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = lean_expr_instantiate_rev_range(v_e_4342_, v_beginIdx_4343_, v_endIdx_4344_, v_subst_4345_);
lean_dec_ref(v_subst_4345_);
lean_dec(v_endIdx_4344_);
lean_dec(v_beginIdx_4343_);
lean_dec_ref(v_e_4342_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4349_, lean_object* v_xs_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = lean_expr_abstract(v_e_4349_, v_xs_4350_);
lean_dec_ref(v_xs_4350_);
lean_dec_ref(v_e_4349_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4355_, lean_object* v_n_4356_, lean_object* v_xs_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = lean_expr_abstract_range(v_e_4355_, v_n_4356_, v_xs_4357_);
lean_dec_ref(v_xs_4357_);
lean_dec(v_n_4356_);
lean_dec_ref(v_e_4355_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4359_, lean_object* v_fvar_4360_, lean_object* v_v_4361_){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4362_ = lean_unsigned_to_nat(1u);
v___x_4363_ = lean_mk_empty_array_with_capacity(v___x_4362_);
v___x_4364_ = lean_array_push(v___x_4363_, v_fvar_4360_);
v___x_4365_ = lean_expr_abstract(v_e_4359_, v___x_4364_);
lean_dec_ref(v___x_4364_);
v___x_4366_ = lean_expr_instantiate1(v___x_4365_, v_v_4361_);
lean_dec_ref(v___x_4365_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4367_, lean_object* v_fvar_4368_, lean_object* v_v_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Lean_Expr_replaceFVar(v_e_4367_, v_fvar_4368_, v_v_4369_);
lean_dec_ref(v_v_4369_);
lean_dec_ref(v_e_4367_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4371_, lean_object* v_fvarId_4372_, lean_object* v_v_4373_){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = l_Lean_Expr_fvar___override(v_fvarId_4372_);
v___x_4375_ = l_Lean_Expr_replaceFVar(v_e_4371_, v___x_4374_, v_v_4373_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4376_, lean_object* v_fvarId_4377_, lean_object* v_v_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_Expr_replaceFVarId(v_e_4376_, v_fvarId_4377_, v_v_4378_);
lean_dec_ref(v_v_4378_);
lean_dec_ref(v_e_4376_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4380_, lean_object* v_fvars_4381_, lean_object* v_vs_4382_){
_start:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = lean_expr_abstract(v_e_4380_, v_fvars_4381_);
v___x_4384_ = lean_expr_instantiate_rev(v___x_4383_, v_vs_4382_);
lean_dec_ref(v___x_4383_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4385_, lean_object* v_fvars_4386_, lean_object* v_vs_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Lean_Expr_replaceFVars(v_e_4385_, v_fvars_4386_, v_vs_4387_);
lean_dec_ref(v_vs_4387_);
lean_dec_ref(v_fvars_4386_);
lean_dec_ref(v_e_4385_);
return v_res_4388_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4391_){
_start:
{
switch(lean_obj_tag(v_x_4391_))
{
case 4:
{
uint8_t v___x_4392_; 
v___x_4392_ = 1;
return v___x_4392_;
}
case 3:
{
uint8_t v___x_4393_; 
v___x_4393_ = 1;
return v___x_4393_;
}
case 0:
{
uint8_t v___x_4394_; 
v___x_4394_ = 1;
return v___x_4394_;
}
case 9:
{
uint8_t v___x_4395_; 
v___x_4395_ = 1;
return v___x_4395_;
}
case 2:
{
uint8_t v___x_4396_; 
v___x_4396_ = 1;
return v___x_4396_;
}
case 1:
{
uint8_t v___x_4397_; 
v___x_4397_ = 1;
return v___x_4397_;
}
default: 
{
uint8_t v___x_4398_; 
v___x_4398_ = 0;
return v___x_4398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4399_){
_start:
{
uint8_t v_res_4400_; lean_object* v_r_4401_; 
v_res_4400_ = l_Lean_Expr_isAtomic(v_x_4399_);
lean_dec_ref(v_x_4399_);
v_r_4401_ = lean_box(v_res_4400_);
return v_r_4401_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4407_ = lean_box(0);
v___x_4408_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4409_ = l_Lean_Expr_const___override(v___x_4408_, v___x_4407_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4410_, lean_object* v_proof_4411_){
_start:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4412_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4413_ = l_Lean_mkAppB(v___x_4412_, v_pred_4410_, v_proof_4411_);
return v___x_4413_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4418_ = lean_box(0);
v___x_4419_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4420_ = l_Lean_Expr_const___override(v___x_4419_, v___x_4418_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4421_, lean_object* v_proof_4422_){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4423_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4424_ = l_Lean_mkAppB(v___x_4423_, v_pred_4421_, v_proof_4422_);
return v___x_4424_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4425_; 
v___x_4425_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4425_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4427_){
_start:
{
lean_inc_ref(v_val_4427_);
return v_val_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4428_);
lean_dec_ref(v_val_4428_);
return v_res_4429_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4432_, lean_object* v_x_4433_){
_start:
{
uint8_t v___x_4434_; 
v___x_4434_ = lean_expr_equal(v_x_4432_, v_x_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4435_, lean_object* v_x_4436_){
_start:
{
uint8_t v_res_4437_; lean_object* v_r_4438_; 
v_res_4437_ = l_Lean_ExprStructEq_beq(v_x_4435_, v_x_4436_);
lean_dec_ref(v_x_4436_);
lean_dec_ref(v_x_4435_);
v_r_4438_ = lean_box(v_res_4437_);
return v_r_4438_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4439_){
_start:
{
uint64_t v___x_4440_; 
v___x_4440_ = l_Lean_Expr_hash(v_x_4439_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4441_){
_start:
{
uint64_t v_res_4442_; lean_object* v_r_4443_; 
v_res_4442_ = l_Lean_ExprStructEq_hash(v_x_4441_);
lean_dec_ref(v_x_4441_);
v_r_4443_ = lean_box_uint64(v_res_4442_);
return v_r_4443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4450_, lean_object* v_start_4451_, lean_object* v_b_4452_, lean_object* v_i_4453_){
_start:
{
uint8_t v___x_4454_; 
v___x_4454_ = lean_nat_dec_le(v_i_4453_, v_start_4451_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v_i_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4455_ = l_Lean_instInhabitedExpr;
v___x_4456_ = lean_unsigned_to_nat(1u);
v_i_4457_ = lean_nat_sub(v_i_4453_, v___x_4456_);
lean_dec(v_i_4453_);
v___x_4458_ = lean_array_get_borrowed(v___x_4455_, v_revArgs_4450_, v_i_4457_);
lean_inc(v___x_4458_);
v___x_4459_ = l_Lean_Expr_app___override(v_b_4452_, v___x_4458_);
v_b_4452_ = v___x_4459_;
v_i_4453_ = v_i_4457_;
goto _start;
}
else
{
lean_dec(v_i_4453_);
return v_b_4452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4461_, lean_object* v_start_4462_, lean_object* v_b_4463_, lean_object* v_i_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4461_, v_start_4462_, v_b_4463_, v_i_4464_);
lean_dec(v_start_4462_);
lean_dec_ref(v_revArgs_4461_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4466_, lean_object* v_beginIdx_4467_, lean_object* v_endIdx_4468_, lean_object* v_revArgs_4469_){
_start:
{
lean_object* v___x_4470_; 
v___x_4470_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4469_, v_beginIdx_4467_, v_f_4466_, v_endIdx_4468_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4471_, lean_object* v_beginIdx_4472_, lean_object* v_endIdx_4473_, lean_object* v_revArgs_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Lean_Expr_mkAppRevRange(v_f_4471_, v_beginIdx_4472_, v_endIdx_4473_, v_revArgs_4474_);
lean_dec_ref(v_revArgs_4474_);
lean_dec(v_beginIdx_4472_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4476_, uint8_t v_useZeta_4477_, uint8_t v_preserveMData_4478_, lean_object* v_sz_4479_, lean_object* v_e_4480_, lean_object* v_i_4481_){
_start:
{
switch(lean_obj_tag(v_e_4480_))
{
case 6:
{
lean_object* v_body_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; uint8_t v___x_4490_; 
v_body_4487_ = lean_ctor_get(v_e_4480_, 2);
lean_inc_ref(v_body_4487_);
lean_dec_ref_known(v_e_4480_, 3);
v___x_4488_ = lean_unsigned_to_nat(1u);
v___x_4489_ = lean_nat_add(v_i_4481_, v___x_4488_);
lean_dec(v_i_4481_);
v___x_4490_ = lean_nat_dec_lt(v___x_4489_, v_sz_4479_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; 
lean_dec(v___x_4489_);
v___x_4491_ = lean_expr_instantiate(v_body_4487_, v_revArgs_4476_);
lean_dec_ref(v_body_4487_);
return v___x_4491_;
}
else
{
v_e_4480_ = v_body_4487_;
v_i_4481_ = v___x_4489_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4477_ == 0)
{
goto v___jp_4482_;
}
else
{
lean_object* v_value_4493_; lean_object* v_body_4494_; uint8_t v___x_4495_; 
v_value_4493_ = lean_ctor_get(v_e_4480_, 2);
v_body_4494_ = lean_ctor_get(v_e_4480_, 3);
v___x_4495_ = lean_nat_dec_lt(v_i_4481_, v_sz_4479_);
if (v___x_4495_ == 0)
{
goto v___jp_4482_;
}
else
{
lean_object* v___x_4496_; 
lean_inc_ref(v_body_4494_);
lean_inc_ref(v_value_4493_);
lean_dec_ref_known(v_e_4480_, 4);
v___x_4496_ = lean_expr_instantiate1(v_body_4494_, v_value_4493_);
lean_dec_ref(v_value_4493_);
lean_dec_ref(v_body_4494_);
v_e_4480_ = v___x_4496_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4478_ == 0)
{
lean_object* v_expr_4498_; 
v_expr_4498_ = lean_ctor_get(v_e_4480_, 1);
lean_inc_ref(v_expr_4498_);
lean_dec_ref_known(v_e_4480_, 2);
v_e_4480_ = v_expr_4498_;
goto _start;
}
else
{
goto v___jp_4482_;
}
}
default: 
{
goto v___jp_4482_;
}
}
v___jp_4482_:
{
lean_object* v_n_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v_n_4483_ = lean_nat_sub(v_sz_4479_, v_i_4481_);
lean_dec(v_i_4481_);
v___x_4484_ = lean_expr_instantiate_range(v_e_4480_, v_n_4483_, v_sz_4479_, v_revArgs_4476_);
lean_dec_ref(v_e_4480_);
v___x_4485_ = lean_unsigned_to_nat(0u);
v___x_4486_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4476_, v___x_4485_, v___x_4484_, v_n_4483_);
return v___x_4486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4500_, lean_object* v_useZeta_4501_, lean_object* v_preserveMData_4502_, lean_object* v_sz_4503_, lean_object* v_e_4504_, lean_object* v_i_4505_){
_start:
{
uint8_t v_useZeta_boxed_4506_; uint8_t v_preserveMData_boxed_4507_; lean_object* v_res_4508_; 
v_useZeta_boxed_4506_ = lean_unbox(v_useZeta_4501_);
v_preserveMData_boxed_4507_ = lean_unbox(v_preserveMData_4502_);
v_res_4508_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4500_, v_useZeta_boxed_4506_, v_preserveMData_boxed_4507_, v_sz_4503_, v_e_4504_, v_i_4505_);
lean_dec(v_sz_4503_);
lean_dec_ref(v_revArgs_4500_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4509_, lean_object* v_revArgs_4510_, uint8_t v_useZeta_4511_, uint8_t v_preserveMData_4512_){
_start:
{
lean_object* v_sz_4513_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v_sz_4513_ = lean_array_get_size(v_revArgs_4510_);
v___x_4514_ = lean_unsigned_to_nat(0u);
v___x_4515_ = lean_nat_dec_eq(v_sz_4513_, v___x_4514_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; 
v___x_4516_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4510_, v_useZeta_4511_, v_preserveMData_4512_, v_sz_4513_, v_f_4509_, v___x_4514_);
return v___x_4516_;
}
else
{
return v_f_4509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4517_, lean_object* v_revArgs_4518_, lean_object* v_useZeta_4519_, lean_object* v_preserveMData_4520_){
_start:
{
uint8_t v_useZeta_boxed_4521_; uint8_t v_preserveMData_boxed_4522_; lean_object* v_res_4523_; 
v_useZeta_boxed_4521_ = lean_unbox(v_useZeta_4519_);
v_preserveMData_boxed_4522_ = lean_unbox(v_preserveMData_4520_);
v_res_4523_ = l_Lean_Expr_betaRev(v_f_4517_, v_revArgs_4518_, v_useZeta_boxed_4521_, v_preserveMData_boxed_4522_);
lean_dec_ref(v_revArgs_4518_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4524_, lean_object* v_args_4525_){
_start:
{
lean_object* v___x_4526_; uint8_t v___x_4527_; lean_object* v___x_4528_; 
v___x_4526_ = l_Array_reverse___redArg(v_args_4525_);
v___x_4527_ = 0;
v___x_4528_ = l_Lean_Expr_betaRev(v_f_4524_, v___x_4526_, v___x_4527_, v___x_4527_);
lean_dec_ref(v___x_4526_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4529_){
_start:
{
switch(lean_obj_tag(v_x_4529_))
{
case 6:
{
lean_object* v_body_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v_body_4530_ = lean_ctor_get(v_x_4529_, 2);
v___x_4531_ = l_Lean_Expr_getNumHeadLambdas(v_body_4530_);
v___x_4532_ = lean_unsigned_to_nat(1u);
v___x_4533_ = lean_nat_add(v___x_4531_, v___x_4532_);
lean_dec(v___x_4531_);
return v___x_4533_;
}
case 10:
{
lean_object* v_expr_4534_; 
v_expr_4534_ = lean_ctor_get(v_x_4529_, 1);
v_x_4529_ = v_expr_4534_;
goto _start;
}
default: 
{
lean_object* v___x_4536_; 
v___x_4536_ = lean_unsigned_to_nat(0u);
return v___x_4536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Lean_Expr_getNumHeadLambdas(v_x_4537_);
lean_dec_ref(v_x_4537_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4539_){
_start:
{
switch(lean_obj_tag(v_x_4539_))
{
case 6:
{
lean_object* v_body_4540_; 
v_body_4540_ = lean_ctor_get(v_x_4539_, 2);
v_x_4539_ = v_body_4540_;
goto _start;
}
case 10:
{
lean_object* v_expr_4542_; 
v_expr_4542_ = lean_ctor_get(v_x_4539_, 1);
v_x_4539_ = v_expr_4542_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4539_);
return v_x_4539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Lean_Expr_getLambdaBody(v_x_4544_);
lean_dec_ref(v_x_4544_);
return v_res_4545_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4546_, lean_object* v_x_4547_){
_start:
{
switch(lean_obj_tag(v_x_4547_))
{
case 6:
{
uint8_t v___x_4548_; 
v___x_4548_ = 1;
return v___x_4548_;
}
case 8:
{
if (v_useZeta_4546_ == 0)
{
return v_useZeta_4546_;
}
else
{
lean_object* v_body_4549_; 
v_body_4549_ = lean_ctor_get(v_x_4547_, 3);
v_x_4547_ = v_body_4549_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4551_; 
v_expr_4551_ = lean_ctor_get(v_x_4547_, 1);
v_x_4547_ = v_expr_4551_;
goto _start;
}
default: 
{
uint8_t v___x_4553_; 
v___x_4553_ = 0;
return v___x_4553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4554_, lean_object* v_x_4555_){
_start:
{
uint8_t v_useZeta_boxed_4556_; uint8_t v_res_4557_; lean_object* v_r_4558_; 
v_useZeta_boxed_4556_ = lean_unbox(v_useZeta_4554_);
v_res_4557_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4556_, v_x_4555_);
lean_dec_ref(v_x_4555_);
v_r_4558_ = lean_box(v_res_4557_);
return v_r_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4559_){
_start:
{
lean_object* v_f_4560_; uint8_t v___x_4561_; uint8_t v___x_4562_; 
v_f_4560_ = l_Lean_Expr_getAppFn(v_e_4559_);
v___x_4561_ = 0;
v___x_4562_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4561_, v_f_4560_);
if (v___x_4562_ == 0)
{
lean_dec_ref(v_f_4560_);
return v_e_4559_;
}
else
{
lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4563_ = l_Lean_Expr_getAppNumArgs(v_e_4559_);
v___x_4564_ = lean_mk_empty_array_with_capacity(v___x_4563_);
lean_dec(v___x_4563_);
v___x_4565_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4559_, v___x_4564_);
v___x_4566_ = l_Lean_Expr_betaRev(v_f_4560_, v___x_4565_, v___x_4561_, v___x_4561_);
lean_dec_ref(v___x_4565_);
return v___x_4566_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4567_, uint8_t v_useZeta_4568_){
_start:
{
uint8_t v___x_4569_; 
v___x_4569_ = l_Lean_Expr_isApp(v_e_4567_);
if (v___x_4569_ == 0)
{
return v___x_4569_;
}
else
{
lean_object* v___x_4570_; uint8_t v___x_4571_; 
v___x_4570_ = l_Lean_Expr_getAppFn(v_e_4567_);
v___x_4571_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4568_, v___x_4570_);
lean_dec_ref(v___x_4570_);
return v___x_4571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4572_, lean_object* v_useZeta_4573_){
_start:
{
uint8_t v_useZeta_boxed_4574_; uint8_t v_res_4575_; lean_object* v_r_4576_; 
v_useZeta_boxed_4574_ = lean_unbox(v_useZeta_4573_);
v_res_4575_ = l_Lean_Expr_isHeadBetaTarget(v_e_4572_, v_useZeta_boxed_4574_);
lean_dec_ref(v_e_4572_);
v_r_4576_ = lean_box(v_res_4575_);
return v_r_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4577_, lean_object* v_x_4578_, lean_object* v_x_4579_){
_start:
{
lean_object* v_f_4581_; 
if (lean_obj_tag(v_x_4577_) == 5)
{
lean_object* v_arg_4585_; 
v_arg_4585_ = lean_ctor_get(v_x_4577_, 1);
if (lean_obj_tag(v_arg_4585_) == 0)
{
lean_object* v_fn_4586_; lean_object* v_deBruijnIndex_4587_; lean_object* v_zero_4588_; uint8_t v_isZero_4589_; 
v_fn_4586_ = lean_ctor_get(v_x_4577_, 0);
v_deBruijnIndex_4587_ = lean_ctor_get(v_arg_4585_, 0);
v_zero_4588_ = lean_unsigned_to_nat(0u);
v_isZero_4589_ = lean_nat_dec_eq(v_x_4578_, v_zero_4588_);
if (v_isZero_4589_ == 1)
{
lean_dec(v_x_4579_);
lean_dec(v_x_4578_);
v_f_4581_ = v_x_4577_;
goto v___jp_4580_;
}
else
{
uint8_t v___x_4590_; 
lean_inc(v_deBruijnIndex_4587_);
lean_inc_ref(v_fn_4586_);
lean_dec_ref_known(v_x_4577_, 2);
v___x_4590_ = lean_nat_dec_eq(v_deBruijnIndex_4587_, v_x_4579_);
lean_dec(v_deBruijnIndex_4587_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; 
lean_dec_ref(v_fn_4586_);
lean_dec(v_x_4579_);
lean_dec(v_x_4578_);
v___x_4591_ = lean_box(0);
return v___x_4591_;
}
else
{
lean_object* v_one_4592_; lean_object* v_n_4593_; lean_object* v___x_4594_; 
v_one_4592_ = lean_unsigned_to_nat(1u);
v_n_4593_ = lean_nat_sub(v_x_4578_, v_one_4592_);
lean_dec(v_x_4578_);
v___x_4594_ = lean_nat_add(v_x_4579_, v_one_4592_);
lean_dec(v_x_4579_);
v_x_4577_ = v_fn_4586_;
v_x_4578_ = v_n_4593_;
v_x_4579_ = v___x_4594_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4596_; uint8_t v_isZero_4597_; 
lean_dec(v_x_4579_);
v_zero_4596_ = lean_unsigned_to_nat(0u);
v_isZero_4597_ = lean_nat_dec_eq(v_x_4578_, v_zero_4596_);
lean_dec(v_x_4578_);
if (v_isZero_4597_ == 1)
{
v_f_4581_ = v_x_4577_;
goto v___jp_4580_;
}
else
{
lean_object* v___x_4598_; 
lean_dec_ref_known(v_x_4577_, 2);
v___x_4598_ = lean_box(0);
return v___x_4598_;
}
}
}
else
{
lean_object* v_zero_4599_; uint8_t v_isZero_4600_; 
lean_dec(v_x_4579_);
v_zero_4599_ = lean_unsigned_to_nat(0u);
v_isZero_4600_ = lean_nat_dec_eq(v_x_4578_, v_zero_4599_);
lean_dec(v_x_4578_);
if (v_isZero_4600_ == 1)
{
v_f_4581_ = v_x_4577_;
goto v___jp_4580_;
}
else
{
lean_object* v___x_4601_; 
lean_dec_ref(v_x_4577_);
v___x_4601_ = lean_box(0);
return v___x_4601_;
}
}
v___jp_4580_:
{
uint8_t v___x_4582_; 
v___x_4582_ = l_Lean_Expr_hasLooseBVars(v_f_4581_);
if (v___x_4582_ == 0)
{
lean_object* v___x_4583_; 
v___x_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4583_, 0, v_f_4581_);
return v___x_4583_;
}
else
{
lean_object* v___x_4584_; 
lean_dec_ref(v_f_4581_);
v___x_4584_ = lean_box(0);
return v___x_4584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4602_, lean_object* v_x_4603_){
_start:
{
if (lean_obj_tag(v_x_4602_) == 6)
{
lean_object* v_body_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v_body_4604_ = lean_ctor_get(v_x_4602_, 2);
lean_inc_ref(v_body_4604_);
lean_dec_ref_known(v_x_4602_, 3);
v___x_4605_ = lean_unsigned_to_nat(1u);
v___x_4606_ = lean_nat_add(v_x_4603_, v___x_4605_);
lean_dec(v_x_4603_);
v_x_4602_ = v_body_4604_;
v_x_4603_ = v___x_4606_;
goto _start;
}
else
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4602_, v_x_4603_, v___x_4608_);
return v___x_4609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4610_){
_start:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4611_ = lean_unsigned_to_nat(0u);
v___x_4612_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4610_, v___x_4611_);
return v___x_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4613_){
_start:
{
if (lean_obj_tag(v_x_4613_) == 6)
{
lean_object* v_body_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v_body_4614_ = lean_ctor_get(v_x_4613_, 2);
lean_inc_ref(v_body_4614_);
lean_dec_ref_known(v_x_4613_, 3);
v___x_4615_ = lean_unsigned_to_nat(1u);
v___x_4616_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4614_, v___x_4615_);
return v___x_4616_;
}
else
{
lean_object* v___x_4617_; 
lean_dec_ref(v_x_4613_);
v___x_4617_ = lean_box(0);
return v___x_4617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4621_){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; uint8_t v___x_4624_; 
v___x_4622_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4628_);
lean_dec_ref(v_e_4628_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4633_){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; 
v___x_4634_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4635_ = lean_unsigned_to_nat(2u);
v___x_4636_ = l_Lean_Expr_isAppOfArity(v_e_4633_, v___x_4634_, v___x_4635_);
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; 
v___x_4637_ = lean_box(0);
return v___x_4637_;
}
else
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = l_Lean_Expr_appArg_x21(v_e_4633_);
v___x_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4638_);
return v___x_4639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4640_);
lean_dec_ref(v_e_4640_);
return v_res_4641_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4645_){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; uint8_t v___x_4648_; 
v___x_4646_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4647_ = lean_unsigned_to_nat(1u);
v___x_4648_ = l_Lean_Expr_isAppOfArity(v_e_4645_, v___x_4646_, v___x_4647_);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4649_){
_start:
{
uint8_t v_res_4650_; lean_object* v_r_4651_; 
v_res_4650_ = l_Lean_Expr_isOutParam(v_e_4649_);
lean_dec_ref(v_e_4649_);
v_r_4651_ = lean_box(v_res_4650_);
return v_r_4651_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4655_){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; uint8_t v___x_4658_; 
v___x_4656_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4657_ = lean_unsigned_to_nat(1u);
v___x_4658_ = l_Lean_Expr_isAppOfArity(v_e_4655_, v___x_4656_, v___x_4657_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4659_){
_start:
{
uint8_t v_res_4660_; lean_object* v_r_4661_; 
v_res_4660_ = l_Lean_Expr_isSemiOutParam(v_e_4659_);
lean_dec_ref(v_e_4659_);
v_r_4661_ = lean_box(v_res_4660_);
return v_r_4661_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4662_){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; uint8_t v___x_4665_; 
v___x_4663_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4664_ = lean_unsigned_to_nat(2u);
v___x_4665_ = l_Lean_Expr_isAppOfArity(v_e_4662_, v___x_4663_, v___x_4664_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4666_){
_start:
{
uint8_t v_res_4667_; lean_object* v_r_4668_; 
v_res_4667_ = l_Lean_Expr_isOptParam(v_e_4666_);
lean_dec_ref(v_e_4666_);
v_r_4668_ = lean_box(v_res_4667_);
return v_r_4668_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4669_){
_start:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; uint8_t v___x_4672_; 
v___x_4670_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4671_ = lean_unsigned_to_nat(2u);
v___x_4672_ = l_Lean_Expr_isAppOfArity(v_e_4669_, v___x_4670_, v___x_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4673_){
_start:
{
uint8_t v_res_4674_; lean_object* v_r_4675_; 
v_res_4674_ = l_Lean_Expr_isAutoParam(v_e_4673_);
lean_dec_ref(v_e_4673_);
v_r_4675_ = lean_box(v_res_4674_);
return v_r_4675_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4676_){
_start:
{
lean_object* v___x_4677_; 
v___x_4677_ = l_Lean_Expr_getAppFn(v_e_4676_);
if (lean_obj_tag(v___x_4677_) == 4)
{
lean_object* v_declName_4678_; lean_object* v___x_4679_; uint8_t v___x_4680_; 
v_declName_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_declName_4678_);
lean_dec_ref_known(v___x_4677_, 2);
v___x_4679_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4680_ = lean_name_eq(v_declName_4678_, v___x_4679_);
if (v___x_4680_ == 0)
{
lean_object* v___x_4681_; uint8_t v___x_4682_; 
v___x_4681_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4682_ = lean_name_eq(v_declName_4678_, v___x_4681_);
if (v___x_4682_ == 0)
{
lean_object* v___x_4683_; uint8_t v___x_4684_; 
v___x_4683_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4684_ = lean_name_eq(v_declName_4678_, v___x_4683_);
if (v___x_4684_ == 0)
{
lean_object* v___x_4685_; uint8_t v___x_4686_; 
v___x_4685_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4686_ = lean_name_eq(v_declName_4678_, v___x_4685_);
lean_dec(v_declName_4678_);
return v___x_4686_;
}
else
{
lean_dec(v_declName_4678_);
return v___x_4684_;
}
}
else
{
lean_dec(v_declName_4678_);
return v___x_4682_;
}
}
else
{
lean_dec(v_declName_4678_);
return v___x_4680_;
}
}
else
{
uint8_t v___x_4687_; 
lean_dec_ref(v___x_4677_);
v___x_4687_ = 0;
return v___x_4687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4688_){
_start:
{
uint8_t v_res_4689_; lean_object* v_r_4690_; 
v_res_4689_ = l_Lean_Expr_isTypeAnnotation(v_e_4688_);
lean_dec_ref(v_e_4688_);
v_r_4690_ = lean_box(v_res_4689_);
return v_r_4690_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4691_){
_start:
{
if (lean_obj_tag(v_e_4691_) == 5)
{
lean_object* v_fn_4692_; 
v_fn_4692_ = lean_ctor_get(v_e_4691_, 0);
switch(lean_obj_tag(v_fn_4692_))
{
case 4:
{
lean_object* v_arg_4693_; lean_object* v_declName_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; 
v_arg_4693_ = lean_ctor_get(v_e_4691_, 1);
v_declName_4694_ = lean_ctor_get(v_fn_4692_, 0);
v___x_4695_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4696_ = lean_name_eq(v_declName_4694_, v___x_4695_);
if (v___x_4696_ == 0)
{
lean_object* v___x_4697_; uint8_t v___x_4698_; 
v___x_4697_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4698_ = lean_name_eq(v_declName_4694_, v___x_4697_);
if (v___x_4698_ == 0)
{
return v_e_4691_;
}
else
{
lean_inc_ref(v_arg_4693_);
lean_dec_ref_known(v_e_4691_, 2);
v_e_4691_ = v_arg_4693_;
goto _start;
}
}
else
{
lean_inc_ref(v_arg_4693_);
lean_dec_ref_known(v_e_4691_, 2);
v_e_4691_ = v_arg_4693_;
goto _start;
}
}
case 5:
{
lean_object* v_fn_4701_; 
v_fn_4701_ = lean_ctor_get(v_fn_4692_, 0);
if (lean_obj_tag(v_fn_4701_) == 4)
{
lean_object* v_arg_4702_; lean_object* v_declName_4703_; lean_object* v___x_4704_; uint8_t v___x_4705_; 
v_arg_4702_ = lean_ctor_get(v_fn_4692_, 1);
v_declName_4703_ = lean_ctor_get(v_fn_4701_, 0);
v___x_4704_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4705_ = lean_name_eq(v_declName_4703_, v___x_4704_);
if (v___x_4705_ == 0)
{
lean_object* v___x_4706_; uint8_t v___x_4707_; 
v___x_4706_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4707_ = lean_name_eq(v_declName_4703_, v___x_4706_);
if (v___x_4707_ == 0)
{
return v_e_4691_;
}
else
{
lean_inc_ref(v_arg_4702_);
lean_dec_ref_known(v_e_4691_, 2);
v_e_4691_ = v_arg_4702_;
goto _start;
}
}
else
{
lean_inc_ref(v_arg_4702_);
lean_dec_ref_known(v_e_4691_, 2);
v_e_4691_ = v_arg_4702_;
goto _start;
}
}
else
{
return v_e_4691_;
}
}
default: 
{
return v_e_4691_;
}
}
}
else
{
return v_e_4691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4710_){
_start:
{
switch(lean_obj_tag(v_e_4710_))
{
case 10:
{
lean_object* v_expr_4711_; 
v_expr_4711_ = lean_ctor_get(v_e_4710_, 1);
v_e_4710_ = v_expr_4711_;
goto _start;
}
case 5:
{
lean_object* v_fn_4713_; 
v_fn_4713_ = lean_ctor_get(v_e_4710_, 0);
switch(lean_obj_tag(v_fn_4713_))
{
case 4:
{
lean_object* v_arg_4714_; lean_object* v_declName_4715_; lean_object* v___x_4716_; uint8_t v___x_4717_; 
v_arg_4714_ = lean_ctor_get(v_e_4710_, 1);
v_declName_4715_ = lean_ctor_get(v_fn_4713_, 0);
v___x_4716_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4717_ = lean_name_eq(v_declName_4715_, v___x_4716_);
if (v___x_4717_ == 0)
{
lean_object* v___x_4718_; uint8_t v___x_4719_; 
v___x_4718_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4719_ = lean_name_eq(v_declName_4715_, v___x_4718_);
if (v___x_4719_ == 0)
{
lean_inc_ref(v_e_4710_);
return v_e_4710_;
}
else
{
v_e_4710_ = v_arg_4714_;
goto _start;
}
}
else
{
v_e_4710_ = v_arg_4714_;
goto _start;
}
}
case 5:
{
lean_object* v_fn_4722_; 
v_fn_4722_ = lean_ctor_get(v_fn_4713_, 0);
if (lean_obj_tag(v_fn_4722_) == 4)
{
lean_object* v_arg_4723_; lean_object* v_declName_4724_; lean_object* v___x_4725_; uint8_t v___x_4726_; 
v_arg_4723_ = lean_ctor_get(v_fn_4713_, 1);
v_declName_4724_ = lean_ctor_get(v_fn_4722_, 0);
v___x_4725_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4726_ = lean_name_eq(v_declName_4724_, v___x_4725_);
if (v___x_4726_ == 0)
{
lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___x_4727_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4728_ = lean_name_eq(v_declName_4724_, v___x_4727_);
if (v___x_4728_ == 0)
{
lean_inc_ref(v_e_4710_);
return v_e_4710_;
}
else
{
v_e_4710_ = v_arg_4723_;
goto _start;
}
}
else
{
v_e_4710_ = v_arg_4723_;
goto _start;
}
}
else
{
lean_inc_ref(v_e_4710_);
return v_e_4710_;
}
}
default: 
{
lean_inc_ref(v_e_4710_);
return v_e_4710_;
}
}
}
default: 
{
lean_inc_ref(v_e_4710_);
return v_e_4710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations___boxed(lean_object* v_e_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Lean_Expr_cleanupAnnotations(v_e_4731_);
lean_dec_ref(v_e_4731_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4733_){
_start:
{
lean_object* v_fn_4734_; lean_object* v___x_4735_; 
v_fn_4734_ = lean_ctor_get(v_e_4733_, 0);
v___x_4735_ = l_Lean_Expr_cleanupAnnotations(v_fn_4734_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg___boxed(lean_object* v_e_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4736_);
lean_dec_ref(v_e_4736_);
return v_res_4737_;
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
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___boxed(lean_object* v_e_4741_, lean_object* v_h_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l_Lean_Expr_appFnCleanup(v_e_4741_, v_h_4742_);
lean_dec_ref(v_e_4741_);
return v_res_4743_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4747_){
_start:
{
lean_object* v___x_4748_; lean_object* v___x_4749_; uint8_t v___x_4750_; 
v___x_4748_ = l_Lean_Expr_cleanupAnnotations(v_e_4747_);
v___x_4749_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4750_ = l_Lean_Expr_isConstOf(v___x_4748_, v___x_4749_);
lean_dec_ref(v___x_4748_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4751_){
_start:
{
uint8_t v_res_4752_; lean_object* v_r_4753_; 
v_res_4752_ = l_Lean_Expr_isFalse(v_e_4751_);
lean_dec_ref(v_e_4751_);
v_r_4753_ = lean_box(v_res_4752_);
return v_r_4753_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4757_){
_start:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; uint8_t v___x_4760_; 
v___x_4758_ = l_Lean_Expr_cleanupAnnotations(v_e_4757_);
v___x_4759_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4760_ = l_Lean_Expr_isConstOf(v___x_4758_, v___x_4759_);
lean_dec_ref(v___x_4758_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4761_){
_start:
{
uint8_t v_res_4762_; lean_object* v_r_4763_; 
v_res_4762_ = l_Lean_Expr_isTrue(v_e_4761_);
lean_dec_ref(v_e_4761_);
v_r_4763_ = lean_box(v_res_4762_);
return v_r_4763_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4769_){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; uint8_t v___x_4772_; 
v___x_4770_ = l_Lean_Expr_cleanupAnnotations(v_e_4769_);
v___x_4771_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__2));
v___x_4772_ = l_Lean_Expr_isConstOf(v___x_4770_, v___x_4771_);
lean_dec_ref(v___x_4770_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4773_){
_start:
{
uint8_t v_res_4774_; lean_object* v_r_4775_; 
v_res_4774_ = l_Lean_Expr_isBoolFalse(v_e_4773_);
lean_dec_ref(v_e_4773_);
v_r_4775_ = lean_box(v_res_4774_);
return v_r_4775_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4779_){
_start:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; 
v___x_4780_ = l_Lean_Expr_cleanupAnnotations(v_e_4779_);
v___x_4781_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4782_ = l_Lean_Expr_isConstOf(v___x_4780_, v___x_4781_);
lean_dec_ref(v___x_4780_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4783_){
_start:
{
uint8_t v_res_4784_; lean_object* v_r_4785_; 
v_res_4784_ = l_Lean_Expr_isBoolTrue(v_e_4783_);
lean_dec_ref(v_e_4783_);
v_r_4785_ = lean_box(v_res_4784_);
return v_r_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4786_){
_start:
{
switch(lean_obj_tag(v_x_4786_))
{
case 10:
{
lean_object* v_expr_4787_; 
v_expr_4787_ = lean_ctor_get(v_x_4786_, 1);
lean_inc_ref(v_expr_4787_);
lean_dec_ref_known(v_x_4786_, 2);
v_x_4786_ = v_expr_4787_;
goto _start;
}
case 7:
{
lean_object* v_body_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
v_body_4789_ = lean_ctor_get(v_x_4786_, 2);
lean_inc_ref(v_body_4789_);
lean_dec_ref_known(v_x_4786_, 3);
v___x_4790_ = l_Lean_Expr_getForallArity(v_body_4789_);
v___x_4791_ = lean_unsigned_to_nat(1u);
v___x_4792_ = lean_nat_add(v___x_4790_, v___x_4791_);
lean_dec(v___x_4790_);
return v___x_4792_;
}
default: 
{
uint8_t v___x_4793_; uint8_t v___x_4794_; 
v___x_4793_ = 0;
v___x_4794_ = l_Lean_Expr_isHeadBetaTarget(v_x_4786_, v___x_4793_);
if (v___x_4794_ == 0)
{
lean_object* v_e_x27_4795_; uint8_t v___x_4796_; 
v_e_x27_4795_ = l_Lean_Expr_cleanupAnnotations(v_x_4786_);
v___x_4796_ = lean_expr_eqv(v_x_4786_, v_e_x27_4795_);
lean_dec_ref(v_x_4786_);
if (v___x_4796_ == 0)
{
v_x_4786_ = v_e_x27_4795_;
goto _start;
}
else
{
lean_object* v___x_4798_; 
lean_dec_ref(v_e_x27_4795_);
v___x_4798_ = lean_unsigned_to_nat(0u);
return v___x_4798_;
}
}
else
{
lean_object* v___x_4799_; 
v___x_4799_ = l_Lean_Expr_headBeta(v_x_4786_);
v_x_4786_ = v___x_4799_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4801_){
_start:
{
lean_object* v___x_4802_; uint8_t v___x_4803_; 
v___x_4802_ = l_Lean_Expr_cleanupAnnotations(v_e_4801_);
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
lean_object* v___x_4805_; uint8_t v___x_4806_; 
v___x_4805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4802_);
lean_dec_ref(v___x_4802_);
v___x_4806_ = l_Lean_Expr_isApp(v___x_4805_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; 
lean_dec_ref(v___x_4805_);
v___x_4807_ = lean_box(0);
return v___x_4807_;
}
else
{
lean_object* v_arg_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v_arg_4808_ = lean_ctor_get(v___x_4805_, 1);
lean_inc_ref(v_arg_4808_);
v___x_4809_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4805_);
lean_dec_ref(v___x_4805_);
v___x_4810_ = l_Lean_Expr_isApp(v___x_4809_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; 
lean_dec_ref(v___x_4809_);
lean_dec_ref(v_arg_4808_);
v___x_4811_ = lean_box(0);
return v___x_4811_;
}
else
{
lean_object* v___x_4812_; lean_object* v___x_4813_; uint8_t v___x_4814_; 
v___x_4812_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4809_);
lean_dec_ref(v___x_4809_);
v___x_4813_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4814_ = l_Lean_Expr_isConstOf(v___x_4812_, v___x_4813_);
lean_dec_ref(v___x_4812_);
if (v___x_4814_ == 0)
{
lean_object* v___x_4815_; 
lean_dec_ref(v_arg_4808_);
v___x_4815_ = lean_box(0);
return v___x_4815_;
}
else
{
if (lean_obj_tag(v_arg_4808_) == 9)
{
lean_object* v_a_4816_; 
v_a_4816_ = lean_ctor_get(v_arg_4808_, 0);
lean_inc_ref(v_a_4816_);
lean_dec_ref_known(v_arg_4808_, 1);
if (lean_obj_tag(v_a_4816_) == 0)
{
lean_object* v_val_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4824_; 
v_val_4817_ = lean_ctor_get(v_a_4816_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v_a_4816_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4819_ = v_a_4816_;
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_val_4817_);
lean_dec(v_a_4816_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4822_; 
if (v_isShared_4820_ == 0)
{
lean_ctor_set_tag(v___x_4819_, 1);
v___x_4822_ = v___x_4819_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_val_4817_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
else
{
lean_object* v___x_4825_; 
lean_dec_ref(v_a_4816_);
v___x_4825_ = lean_box(0);
return v___x_4825_;
}
}
else
{
lean_object* v___x_4826_; 
lean_dec_ref(v_arg_4808_);
v___x_4826_ = lean_box(0);
return v___x_4826_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f___boxed(lean_object* v_e_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_Lean_Expr_nat_x3f(v_e_4827_);
lean_dec_ref(v_e_4827_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4834_){
_start:
{
lean_object* v___x_4847_; uint8_t v___x_4848_; 
v___x_4847_ = l_Lean_Expr_cleanupAnnotations(v_e_4834_);
v___x_4848_ = l_Lean_Expr_isApp(v___x_4847_);
if (v___x_4848_ == 0)
{
lean_dec_ref(v___x_4847_);
goto v___jp_4835_;
}
else
{
lean_object* v_arg_4849_; lean_object* v___x_4850_; uint8_t v___x_4851_; 
v_arg_4849_ = lean_ctor_get(v___x_4847_, 1);
lean_inc_ref(v_arg_4849_);
v___x_4850_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4847_);
lean_dec_ref(v___x_4847_);
v___x_4851_ = l_Lean_Expr_isApp(v___x_4850_);
if (v___x_4851_ == 0)
{
lean_dec_ref(v___x_4850_);
lean_dec_ref(v_arg_4849_);
goto v___jp_4835_;
}
else
{
lean_object* v___x_4852_; uint8_t v___x_4853_; 
v___x_4852_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4850_);
lean_dec_ref(v___x_4850_);
v___x_4853_ = l_Lean_Expr_isApp(v___x_4852_);
if (v___x_4853_ == 0)
{
lean_dec_ref(v___x_4852_);
lean_dec_ref(v_arg_4849_);
goto v___jp_4835_;
}
else
{
lean_object* v___x_4854_; lean_object* v___x_4855_; uint8_t v___x_4856_; 
v___x_4854_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4852_);
lean_dec_ref(v___x_4852_);
v___x_4855_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4856_ = l_Lean_Expr_isConstOf(v___x_4854_, v___x_4855_);
lean_dec_ref(v___x_4854_);
if (v___x_4856_ == 0)
{
lean_dec_ref(v_arg_4849_);
goto v___jp_4835_;
}
else
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Lean_Expr_nat_x3f(v_arg_4849_);
lean_dec_ref(v_arg_4849_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v___x_4858_; 
v___x_4858_ = lean_box(0);
return v___x_4858_;
}
else
{
lean_object* v_val_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4871_; 
v_val_4859_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4861_ = v___x_4857_;
v_isShared_4862_ = v_isSharedCheck_4871_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_val_4859_);
lean_dec(v___x_4857_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4871_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4863_; uint8_t v___x_4864_; 
v___x_4863_ = lean_unsigned_to_nat(0u);
v___x_4864_ = lean_nat_dec_eq(v_val_4859_, v___x_4863_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4868_; 
v___x_4865_ = lean_nat_to_int(v_val_4859_);
v___x_4866_ = lean_int_neg(v___x_4865_);
lean_dec(v___x_4865_);
if (v_isShared_4862_ == 0)
{
lean_ctor_set(v___x_4861_, 0, v___x_4866_);
v___x_4868_ = v___x_4861_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4866_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
else
{
lean_object* v___x_4870_; 
lean_del_object(v___x_4861_);
lean_dec(v_val_4859_);
v___x_4870_ = lean_box(0);
return v___x_4870_;
}
}
}
}
}
}
}
v___jp_4835_:
{
lean_object* v___x_4836_; 
v___x_4836_ = l_Lean_Expr_nat_x3f(v_e_4834_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v___x_4837_; 
v___x_4837_ = lean_box(0);
return v___x_4837_;
}
else
{
lean_object* v_val_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4846_; 
v_val_4838_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4840_ = v___x_4836_;
v_isShared_4841_ = v_isSharedCheck_4846_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_val_4838_);
lean_dec(v___x_4836_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4846_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4842_; lean_object* v___x_4844_; 
v___x_4842_ = lean_nat_to_int(v_val_4838_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 0, v___x_4842_);
v___x_4844_ = v___x_4840_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4842_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f___boxed(lean_object* v_e_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_Lean_Expr_int_x3f(v_e_4872_);
lean_dec_ref(v_e_4872_);
return v_res_4873_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4874_, lean_object* v_e_4875_){
_start:
{
uint8_t v___x_4876_; lean_object* v_d_4878_; lean_object* v_b_4879_; 
v___x_4876_ = l_Lean_Expr_hasFVar(v_e_4875_);
if (v___x_4876_ == 0)
{
lean_dec_ref(v_e_4875_);
lean_dec_ref(v_p_4874_);
return v___x_4876_;
}
else
{
switch(lean_obj_tag(v_e_4875_))
{
case 7:
{
lean_object* v_binderType_4882_; lean_object* v_body_4883_; 
v_binderType_4882_ = lean_ctor_get(v_e_4875_, 1);
lean_inc_ref(v_binderType_4882_);
v_body_4883_ = lean_ctor_get(v_e_4875_, 2);
lean_inc_ref(v_body_4883_);
lean_dec_ref_known(v_e_4875_, 3);
v_d_4878_ = v_binderType_4882_;
v_b_4879_ = v_body_4883_;
goto v___jp_4877_;
}
case 6:
{
lean_object* v_binderType_4884_; lean_object* v_body_4885_; 
v_binderType_4884_ = lean_ctor_get(v_e_4875_, 1);
lean_inc_ref(v_binderType_4884_);
v_body_4885_ = lean_ctor_get(v_e_4875_, 2);
lean_inc_ref(v_body_4885_);
lean_dec_ref_known(v_e_4875_, 3);
v_d_4878_ = v_binderType_4884_;
v_b_4879_ = v_body_4885_;
goto v___jp_4877_;
}
case 10:
{
lean_object* v_expr_4886_; 
v_expr_4886_ = lean_ctor_get(v_e_4875_, 1);
lean_inc_ref(v_expr_4886_);
lean_dec_ref_known(v_e_4875_, 2);
v_e_4875_ = v_expr_4886_;
goto _start;
}
case 8:
{
lean_object* v_type_4888_; lean_object* v_value_4889_; lean_object* v_body_4890_; uint8_t v___x_4891_; 
v_type_4888_ = lean_ctor_get(v_e_4875_, 1);
lean_inc_ref(v_type_4888_);
v_value_4889_ = lean_ctor_get(v_e_4875_, 2);
lean_inc_ref(v_value_4889_);
v_body_4890_ = lean_ctor_get(v_e_4875_, 3);
lean_inc_ref(v_body_4890_);
lean_dec_ref_known(v_e_4875_, 4);
lean_inc_ref(v_p_4874_);
v___x_4891_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4874_, v_type_4888_);
if (v___x_4891_ == 0)
{
uint8_t v___x_4892_; 
lean_inc_ref(v_p_4874_);
v___x_4892_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4874_, v_value_4889_);
if (v___x_4892_ == 0)
{
v_e_4875_ = v_body_4890_;
goto _start;
}
else
{
lean_dec_ref(v_body_4890_);
lean_dec_ref(v_p_4874_);
return v___x_4876_;
}
}
else
{
lean_dec_ref(v_body_4890_);
lean_dec_ref(v_value_4889_);
lean_dec_ref(v_p_4874_);
return v___x_4876_;
}
}
case 5:
{
lean_object* v_fn_4894_; lean_object* v_arg_4895_; uint8_t v___x_4896_; 
v_fn_4894_ = lean_ctor_get(v_e_4875_, 0);
lean_inc_ref(v_fn_4894_);
v_arg_4895_ = lean_ctor_get(v_e_4875_, 1);
lean_inc_ref(v_arg_4895_);
lean_dec_ref_known(v_e_4875_, 2);
lean_inc_ref(v_p_4874_);
v___x_4896_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4874_, v_fn_4894_);
if (v___x_4896_ == 0)
{
v_e_4875_ = v_arg_4895_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4895_);
lean_dec_ref(v_p_4874_);
return v___x_4876_;
}
}
case 11:
{
lean_object* v_struct_4898_; 
v_struct_4898_ = lean_ctor_get(v_e_4875_, 2);
lean_inc_ref(v_struct_4898_);
lean_dec_ref_known(v_e_4875_, 3);
v_e_4875_ = v_struct_4898_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4900_; lean_object* v___x_4901_; uint8_t v___x_4902_; 
v_fvarId_4900_ = lean_ctor_get(v_e_4875_, 0);
lean_inc(v_fvarId_4900_);
lean_dec_ref_known(v_e_4875_, 1);
v___x_4901_ = lean_apply_1(v_p_4874_, v_fvarId_4900_);
v___x_4902_ = lean_unbox(v___x_4901_);
return v___x_4902_;
}
default: 
{
uint8_t v___x_4903_; 
lean_dec_ref(v_e_4875_);
lean_dec_ref(v_p_4874_);
v___x_4903_ = 0;
return v___x_4903_;
}
}
}
v___jp_4877_:
{
uint8_t v___x_4880_; 
lean_inc_ref(v_p_4874_);
v___x_4880_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4874_, v_d_4878_);
if (v___x_4880_ == 0)
{
v_e_4875_ = v_b_4879_;
goto _start;
}
else
{
lean_dec_ref(v_b_4879_);
lean_dec_ref(v_p_4874_);
return v___x_4876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4904_, lean_object* v_e_4905_){
_start:
{
uint8_t v_res_4906_; lean_object* v_r_4907_; 
v_res_4906_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4904_, v_e_4905_);
v_r_4907_ = lean_box(v_res_4906_);
return v_r_4907_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4908_, lean_object* v_p_4909_){
_start:
{
uint8_t v___x_4910_; 
v___x_4910_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4909_, v_e_4908_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4911_, lean_object* v_p_4912_){
_start:
{
uint8_t v_res_4913_; lean_object* v_r_4914_; 
v_res_4913_ = l_Lean_Expr_hasAnyFVar(v_e_4911_, v_p_4912_);
v_r_4914_ = lean_box(v_res_4913_);
return v_r_4914_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4915_, lean_object* v_e_4916_){
_start:
{
uint8_t v___x_4917_; lean_object* v_d_4919_; lean_object* v_b_4920_; 
v___x_4917_ = l_Lean_Expr_hasFVar(v_e_4916_);
if (v___x_4917_ == 0)
{
return v___x_4917_;
}
else
{
switch(lean_obj_tag(v_e_4916_))
{
case 7:
{
lean_object* v_binderType_4923_; lean_object* v_body_4924_; 
v_binderType_4923_ = lean_ctor_get(v_e_4916_, 1);
v_body_4924_ = lean_ctor_get(v_e_4916_, 2);
v_d_4919_ = v_binderType_4923_;
v_b_4920_ = v_body_4924_;
goto v___jp_4918_;
}
case 6:
{
lean_object* v_binderType_4925_; lean_object* v_body_4926_; 
v_binderType_4925_ = lean_ctor_get(v_e_4916_, 1);
v_body_4926_ = lean_ctor_get(v_e_4916_, 2);
v_d_4919_ = v_binderType_4925_;
v_b_4920_ = v_body_4926_;
goto v___jp_4918_;
}
case 10:
{
lean_object* v_expr_4927_; 
v_expr_4927_ = lean_ctor_get(v_e_4916_, 1);
v_e_4916_ = v_expr_4927_;
goto _start;
}
case 8:
{
lean_object* v_type_4929_; lean_object* v_value_4930_; lean_object* v_body_4931_; uint8_t v___x_4932_; 
v_type_4929_ = lean_ctor_get(v_e_4916_, 1);
v_value_4930_ = lean_ctor_get(v_e_4916_, 2);
v_body_4931_ = lean_ctor_get(v_e_4916_, 3);
v___x_4932_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4915_, v_type_4929_);
if (v___x_4932_ == 0)
{
uint8_t v___x_4933_; 
v___x_4933_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4915_, v_value_4930_);
if (v___x_4933_ == 0)
{
v_e_4916_ = v_body_4931_;
goto _start;
}
else
{
return v___x_4917_;
}
}
else
{
return v___x_4917_;
}
}
case 5:
{
lean_object* v_fn_4935_; lean_object* v_arg_4936_; uint8_t v___x_4937_; 
v_fn_4935_ = lean_ctor_get(v_e_4916_, 0);
v_arg_4936_ = lean_ctor_get(v_e_4916_, 1);
v___x_4937_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4915_, v_fn_4935_);
if (v___x_4937_ == 0)
{
v_e_4916_ = v_arg_4936_;
goto _start;
}
else
{
return v___x_4917_;
}
}
case 11:
{
lean_object* v_struct_4939_; 
v_struct_4939_ = lean_ctor_get(v_e_4916_, 2);
v_e_4916_ = v_struct_4939_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4941_; uint8_t v___x_4942_; 
v_fvarId_4941_ = lean_ctor_get(v_e_4916_, 0);
v___x_4942_ = lean_name_eq(v_fvarId_4941_, v_fvarId_4915_);
return v___x_4942_;
}
default: 
{
uint8_t v___x_4943_; 
v___x_4943_ = 0;
return v___x_4943_;
}
}
}
v___jp_4918_:
{
uint8_t v___x_4921_; 
v___x_4921_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4915_, v_d_4919_);
if (v___x_4921_ == 0)
{
v_e_4916_ = v_b_4920_;
goto _start;
}
else
{
return v___x_4917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4944_, lean_object* v_e_4945_){
_start:
{
uint8_t v_res_4946_; lean_object* v_r_4947_; 
v_res_4946_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4944_, v_e_4945_);
lean_dec_ref(v_e_4945_);
lean_dec(v_fvarId_4944_);
v_r_4947_ = lean_box(v_res_4946_);
return v_r_4947_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4948_, lean_object* v_fvarId_4949_){
_start:
{
uint8_t v___x_4950_; 
v___x_4950_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4949_, v_e_4948_);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4951_, lean_object* v_fvarId_4952_){
_start:
{
uint8_t v_res_4953_; lean_object* v_r_4954_; 
v_res_4953_ = l_Lean_Expr_containsFVar(v_e_4951_, v_fvarId_4952_);
lean_dec(v_fvarId_4952_);
lean_dec_ref(v_e_4951_);
v_r_4954_ = lean_box(v_res_4953_);
return v_r_4954_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(lean_object* v_p_4955_, lean_object* v_e_4956_){
_start:
{
uint8_t v___x_4957_; lean_object* v_d_4959_; lean_object* v_b_4960_; 
v___x_4957_ = l_Lean_Expr_hasExprMVar(v_e_4956_);
if (v___x_4957_ == 0)
{
lean_dec_ref(v_e_4956_);
lean_dec_ref(v_p_4955_);
return v___x_4957_;
}
else
{
switch(lean_obj_tag(v_e_4956_))
{
case 7:
{
lean_object* v_binderType_4963_; lean_object* v_body_4964_; 
v_binderType_4963_ = lean_ctor_get(v_e_4956_, 1);
lean_inc_ref(v_binderType_4963_);
v_body_4964_ = lean_ctor_get(v_e_4956_, 2);
lean_inc_ref(v_body_4964_);
lean_dec_ref_known(v_e_4956_, 3);
v_d_4959_ = v_binderType_4963_;
v_b_4960_ = v_body_4964_;
goto v___jp_4958_;
}
case 6:
{
lean_object* v_binderType_4965_; lean_object* v_body_4966_; 
v_binderType_4965_ = lean_ctor_get(v_e_4956_, 1);
lean_inc_ref(v_binderType_4965_);
v_body_4966_ = lean_ctor_get(v_e_4956_, 2);
lean_inc_ref(v_body_4966_);
lean_dec_ref_known(v_e_4956_, 3);
v_d_4959_ = v_binderType_4965_;
v_b_4960_ = v_body_4966_;
goto v___jp_4958_;
}
case 10:
{
lean_object* v_expr_4967_; 
v_expr_4967_ = lean_ctor_get(v_e_4956_, 1);
lean_inc_ref(v_expr_4967_);
lean_dec_ref_known(v_e_4956_, 2);
v_e_4956_ = v_expr_4967_;
goto _start;
}
case 8:
{
lean_object* v_type_4969_; lean_object* v_value_4970_; lean_object* v_body_4971_; uint8_t v___x_4972_; 
v_type_4969_ = lean_ctor_get(v_e_4956_, 1);
lean_inc_ref(v_type_4969_);
v_value_4970_ = lean_ctor_get(v_e_4956_, 2);
lean_inc_ref(v_value_4970_);
v_body_4971_ = lean_ctor_get(v_e_4956_, 3);
lean_inc_ref(v_body_4971_);
lean_dec_ref_known(v_e_4956_, 4);
lean_inc_ref(v_p_4955_);
v___x_4972_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4955_, v_type_4969_);
if (v___x_4972_ == 0)
{
uint8_t v___x_4973_; 
lean_inc_ref(v_p_4955_);
v___x_4973_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4955_, v_value_4970_);
if (v___x_4973_ == 0)
{
v_e_4956_ = v_body_4971_;
goto _start;
}
else
{
lean_dec_ref(v_body_4971_);
lean_dec_ref(v_p_4955_);
return v___x_4957_;
}
}
else
{
lean_dec_ref(v_body_4971_);
lean_dec_ref(v_value_4970_);
lean_dec_ref(v_p_4955_);
return v___x_4957_;
}
}
case 5:
{
lean_object* v_fn_4975_; lean_object* v_arg_4976_; uint8_t v___x_4977_; 
v_fn_4975_ = lean_ctor_get(v_e_4956_, 0);
lean_inc_ref(v_fn_4975_);
v_arg_4976_ = lean_ctor_get(v_e_4956_, 1);
lean_inc_ref(v_arg_4976_);
lean_dec_ref_known(v_e_4956_, 2);
lean_inc_ref(v_p_4955_);
v___x_4977_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4955_, v_fn_4975_);
if (v___x_4977_ == 0)
{
v_e_4956_ = v_arg_4976_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4976_);
lean_dec_ref(v_p_4955_);
return v___x_4957_;
}
}
case 11:
{
lean_object* v_struct_4979_; 
v_struct_4979_ = lean_ctor_get(v_e_4956_, 2);
lean_inc_ref(v_struct_4979_);
lean_dec_ref_known(v_e_4956_, 3);
v_e_4956_ = v_struct_4979_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_4981_; lean_object* v___x_4982_; uint8_t v___x_4983_; 
v_mvarId_4981_ = lean_ctor_get(v_e_4956_, 0);
lean_inc(v_mvarId_4981_);
lean_dec_ref_known(v_e_4956_, 1);
v___x_4982_ = lean_apply_1(v_p_4955_, v_mvarId_4981_);
v___x_4983_ = lean_unbox(v___x_4982_);
return v___x_4983_;
}
default: 
{
uint8_t v___x_4984_; 
lean_dec_ref(v_e_4956_);
lean_dec_ref(v_p_4955_);
v___x_4984_ = 0;
return v___x_4984_;
}
}
}
v___jp_4958_:
{
uint8_t v___x_4961_; 
lean_inc_ref(v_p_4955_);
v___x_4961_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4955_, v_d_4959_);
if (v___x_4961_ == 0)
{
v_e_4956_ = v_b_4960_;
goto _start;
}
else
{
lean_dec_ref(v_b_4960_);
lean_dec_ref(v_p_4955_);
return v___x_4957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___boxed(lean_object* v_p_4985_, lean_object* v_e_4986_){
_start:
{
uint8_t v_res_4987_; lean_object* v_r_4988_; 
v_res_4987_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4985_, v_e_4986_);
v_r_4988_ = lean_box(v_res_4987_);
return v_r_4988_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyMVar(lean_object* v_e_4989_, lean_object* v_p_4990_){
_start:
{
uint8_t v___x_4991_; 
v___x_4991_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4990_, v_e_4989_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyMVar___boxed(lean_object* v_e_4992_, lean_object* v_p_4993_){
_start:
{
uint8_t v_res_4994_; lean_object* v_r_4995_; 
v_res_4994_ = l_Lean_Expr_hasAnyMVar(v_e_4992_, v_p_4993_);
v_r_4995_ = lean_box(v_res_4994_);
return v_r_4995_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(lean_object* v_mvarId_4996_, lean_object* v_e_4997_){
_start:
{
uint8_t v___x_4998_; lean_object* v_d_5000_; lean_object* v_b_5001_; 
v___x_4998_ = l_Lean_Expr_hasExprMVar(v_e_4997_);
if (v___x_4998_ == 0)
{
return v___x_4998_;
}
else
{
switch(lean_obj_tag(v_e_4997_))
{
case 7:
{
lean_object* v_binderType_5004_; lean_object* v_body_5005_; 
v_binderType_5004_ = lean_ctor_get(v_e_4997_, 1);
v_body_5005_ = lean_ctor_get(v_e_4997_, 2);
v_d_5000_ = v_binderType_5004_;
v_b_5001_ = v_body_5005_;
goto v___jp_4999_;
}
case 6:
{
lean_object* v_binderType_5006_; lean_object* v_body_5007_; 
v_binderType_5006_ = lean_ctor_get(v_e_4997_, 1);
v_body_5007_ = lean_ctor_get(v_e_4997_, 2);
v_d_5000_ = v_binderType_5006_;
v_b_5001_ = v_body_5007_;
goto v___jp_4999_;
}
case 10:
{
lean_object* v_expr_5008_; 
v_expr_5008_ = lean_ctor_get(v_e_4997_, 1);
v_e_4997_ = v_expr_5008_;
goto _start;
}
case 8:
{
lean_object* v_type_5010_; lean_object* v_value_5011_; lean_object* v_body_5012_; uint8_t v___x_5013_; 
v_type_5010_ = lean_ctor_get(v_e_4997_, 1);
v_value_5011_ = lean_ctor_get(v_e_4997_, 2);
v_body_5012_ = lean_ctor_get(v_e_4997_, 3);
v___x_5013_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4996_, v_type_5010_);
if (v___x_5013_ == 0)
{
uint8_t v___x_5014_; 
v___x_5014_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4996_, v_value_5011_);
if (v___x_5014_ == 0)
{
v_e_4997_ = v_body_5012_;
goto _start;
}
else
{
return v___x_4998_;
}
}
else
{
return v___x_4998_;
}
}
case 5:
{
lean_object* v_fn_5016_; lean_object* v_arg_5017_; uint8_t v___x_5018_; 
v_fn_5016_ = lean_ctor_get(v_e_4997_, 0);
v_arg_5017_ = lean_ctor_get(v_e_4997_, 1);
v___x_5018_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4996_, v_fn_5016_);
if (v___x_5018_ == 0)
{
v_e_4997_ = v_arg_5017_;
goto _start;
}
else
{
return v___x_4998_;
}
}
case 11:
{
lean_object* v_struct_5020_; 
v_struct_5020_ = lean_ctor_get(v_e_4997_, 2);
v_e_4997_ = v_struct_5020_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_5022_; uint8_t v___x_5023_; 
v_mvarId_5022_ = lean_ctor_get(v_e_4997_, 0);
v___x_5023_ = lean_name_eq(v_mvarId_5022_, v_mvarId_4996_);
return v___x_5023_;
}
default: 
{
uint8_t v___x_5024_; 
v___x_5024_ = 0;
return v___x_5024_;
}
}
}
v___jp_4999_:
{
uint8_t v___x_5002_; 
v___x_5002_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4996_, v_d_5000_);
if (v___x_5002_ == 0)
{
v_e_4997_ = v_b_5001_;
goto _start;
}
else
{
return v___x_4998_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0___boxed(lean_object* v_mvarId_5025_, lean_object* v_e_5026_){
_start:
{
uint8_t v_res_5027_; lean_object* v_r_5028_; 
v_res_5027_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5025_, v_e_5026_);
lean_dec_ref(v_e_5026_);
lean_dec(v_mvarId_5025_);
v_r_5028_ = lean_box(v_res_5027_);
return v_r_5028_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsMVar(lean_object* v_e_5029_, lean_object* v_mvarId_5030_){
_start:
{
uint8_t v___x_5031_; 
v___x_5031_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5030_, v_e_5029_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsMVar___boxed(lean_object* v_e_5032_, lean_object* v_mvarId_5033_){
_start:
{
uint8_t v_res_5034_; lean_object* v_r_5035_; 
v_res_5034_ = l_Lean_Expr_containsMVar(v_e_5032_, v_mvarId_5033_);
lean_dec(v_mvarId_5033_);
lean_dec_ref(v_e_5032_);
v_r_5035_ = lean_box(v_res_5034_);
return v_r_5035_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5037_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_5038_ = lean_unsigned_to_nat(18u);
v___x_5039_ = lean_unsigned_to_nat(1913u);
v___x_5040_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_5041_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5042_ = l_mkPanicMessageWithDecl(v___x_5041_, v___x_5040_, v___x_5039_, v___x_5038_, v___x_5037_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_5043_, lean_object* v_newFn_5044_, lean_object* v_newArg_5045_){
_start:
{
if (lean_obj_tag(v_e_5043_) == 5)
{
lean_object* v_fn_5046_; lean_object* v_arg_5047_; size_t v___x_5048_; size_t v___x_5049_; uint8_t v___x_5050_; 
v_fn_5046_ = lean_ctor_get(v_e_5043_, 0);
v_arg_5047_ = lean_ctor_get(v_e_5043_, 1);
v___x_5048_ = lean_ptr_addr(v_fn_5046_);
v___x_5049_ = lean_ptr_addr(v_newFn_5044_);
v___x_5050_ = lean_usize_dec_eq(v___x_5048_, v___x_5049_);
if (v___x_5050_ == 0)
{
lean_object* v___x_5051_; 
v___x_5051_ = l_Lean_Expr_app___override(v_newFn_5044_, v_newArg_5045_);
return v___x_5051_;
}
else
{
size_t v___x_5052_; size_t v___x_5053_; uint8_t v___x_5054_; 
v___x_5052_ = lean_ptr_addr(v_arg_5047_);
v___x_5053_ = lean_ptr_addr(v_newArg_5045_);
v___x_5054_ = lean_usize_dec_eq(v___x_5052_, v___x_5053_);
if (v___x_5054_ == 0)
{
lean_object* v___x_5055_; 
v___x_5055_ = l_Lean_Expr_app___override(v_newFn_5044_, v_newArg_5045_);
return v___x_5055_;
}
else
{
lean_dec_ref(v_newArg_5045_);
lean_dec_ref(v_newFn_5044_);
lean_inc_ref(v_e_5043_);
return v_e_5043_;
}
}
}
else
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
lean_dec_ref(v_newArg_5045_);
lean_dec_ref(v_newFn_5044_);
v___x_5056_ = l_Lean_instInhabitedExpr;
v___x_5057_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_5058_ = l_panic___redArg(v___x_5056_, v___x_5057_);
return v___x_5058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_5059_, lean_object* v_newFn_5060_, lean_object* v_newArg_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_5059_, v_newFn_5060_, v_newArg_5061_);
lean_dec_ref(v_e_5059_);
return v_res_5062_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5064_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_5065_ = lean_unsigned_to_nat(20u);
v___x_5066_ = lean_unsigned_to_nat(1924u);
v___x_5067_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_5068_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5069_ = l_mkPanicMessageWithDecl(v___x_5068_, v___x_5067_, v___x_5066_, v___x_5065_, v___x_5064_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_5070_, lean_object* v_fvarIdNew_5071_){
_start:
{
if (lean_obj_tag(v_e_5070_) == 1)
{
lean_object* v_fvarId_5072_; uint8_t v___x_5073_; 
v_fvarId_5072_ = lean_ctor_get(v_e_5070_, 0);
v___x_5073_ = lean_name_eq(v_fvarId_5072_, v_fvarIdNew_5071_);
if (v___x_5073_ == 0)
{
lean_object* v___x_5074_; 
v___x_5074_ = l_Lean_Expr_fvar___override(v_fvarIdNew_5071_);
return v___x_5074_;
}
else
{
lean_dec(v_fvarIdNew_5071_);
lean_inc_ref(v_e_5070_);
return v_e_5070_;
}
}
else
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
lean_dec(v_fvarIdNew_5071_);
v___x_5075_ = l_Lean_instInhabitedExpr;
v___x_5076_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_5077_ = l_panic___redArg(v___x_5075_, v___x_5076_);
return v___x_5077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_5078_, lean_object* v_fvarIdNew_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_Expr_updateFVar_x21(v_e_5078_, v_fvarIdNew_5079_);
lean_dec_ref(v_e_5078_);
return v_res_5080_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5082_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_5083_ = lean_unsigned_to_nat(18u);
v___x_5084_ = lean_unsigned_to_nat(1929u);
v___x_5085_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_5086_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5087_ = l_mkPanicMessageWithDecl(v___x_5086_, v___x_5085_, v___x_5084_, v___x_5083_, v___x_5082_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_5088_, lean_object* v_newLevels_5089_){
_start:
{
if (lean_obj_tag(v_e_5088_) == 4)
{
lean_object* v_declName_5090_; lean_object* v_us_5091_; uint8_t v___x_5092_; 
v_declName_5090_ = lean_ctor_get(v_e_5088_, 0);
v_us_5091_ = lean_ctor_get(v_e_5088_, 1);
v___x_5092_ = l_ptrEqList___redArg(v_us_5091_, v_newLevels_5089_);
if (v___x_5092_ == 0)
{
lean_object* v___x_5093_; 
lean_inc(v_declName_5090_);
lean_dec_ref_known(v_e_5088_, 2);
v___x_5093_ = l_Lean_Expr_const___override(v_declName_5090_, v_newLevels_5089_);
return v___x_5093_;
}
else
{
lean_dec(v_newLevels_5089_);
return v_e_5088_;
}
}
else
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
lean_dec(v_newLevels_5089_);
lean_dec_ref(v_e_5088_);
v___x_5094_ = l_Lean_instInhabitedExpr;
v___x_5095_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_5096_ = l_panic___redArg(v___x_5094_, v___x_5095_);
return v___x_5096_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5099_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_5100_ = lean_unsigned_to_nat(14u);
v___x_5101_ = lean_unsigned_to_nat(1940u);
v___x_5102_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_5103_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5104_ = l_mkPanicMessageWithDecl(v___x_5103_, v___x_5102_, v___x_5101_, v___x_5100_, v___x_5099_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_5105_, lean_object* v_u_x27_5106_){
_start:
{
if (lean_obj_tag(v_e_5105_) == 3)
{
lean_object* v_u_5107_; size_t v___x_5108_; size_t v___x_5109_; uint8_t v___x_5110_; 
v_u_5107_ = lean_ctor_get(v_e_5105_, 0);
v___x_5108_ = lean_ptr_addr(v_u_5107_);
v___x_5109_ = lean_ptr_addr(v_u_x27_5106_);
v___x_5110_ = lean_usize_dec_eq(v___x_5108_, v___x_5109_);
if (v___x_5110_ == 0)
{
lean_object* v___x_5111_; 
v___x_5111_ = l_Lean_Expr_sort___override(v_u_x27_5106_);
return v___x_5111_;
}
else
{
lean_dec(v_u_x27_5106_);
lean_inc_ref(v_e_5105_);
return v_e_5105_;
}
}
else
{
lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; 
lean_dec(v_u_x27_5106_);
v___x_5112_ = l_Lean_instInhabitedExpr;
v___x_5113_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5114_ = l_panic___redArg(v___x_5112_, v___x_5113_);
return v___x_5114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5115_, lean_object* v_u_x27_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5115_, v_u_x27_5116_);
lean_dec_ref(v_e_5115_);
return v_res_5117_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
v___x_5120_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5121_ = lean_unsigned_to_nat(17u);
v___x_5122_ = lean_unsigned_to_nat(1951u);
v___x_5123_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5124_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5125_ = l_mkPanicMessageWithDecl(v___x_5124_, v___x_5123_, v___x_5122_, v___x_5121_, v___x_5120_);
return v___x_5125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5126_, lean_object* v_newExpr_5127_){
_start:
{
if (lean_obj_tag(v_e_5126_) == 10)
{
lean_object* v_data_5128_; lean_object* v_expr_5129_; size_t v___x_5130_; size_t v___x_5131_; uint8_t v___x_5132_; 
v_data_5128_ = lean_ctor_get(v_e_5126_, 0);
v_expr_5129_ = lean_ctor_get(v_e_5126_, 1);
v___x_5130_ = lean_ptr_addr(v_expr_5129_);
v___x_5131_ = lean_ptr_addr(v_newExpr_5127_);
v___x_5132_ = lean_usize_dec_eq(v___x_5130_, v___x_5131_);
if (v___x_5132_ == 0)
{
lean_object* v___x_5133_; 
lean_inc(v_data_5128_);
lean_dec_ref_known(v_e_5126_, 2);
v___x_5133_ = l_Lean_Expr_mdata___override(v_data_5128_, v_newExpr_5127_);
return v___x_5133_;
}
else
{
lean_dec_ref(v_newExpr_5127_);
return v_e_5126_;
}
}
else
{
lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; 
lean_dec_ref(v_newExpr_5127_);
lean_dec_ref(v_e_5126_);
v___x_5134_ = l_Lean_instInhabitedExpr;
v___x_5135_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5136_ = l_panic___redArg(v___x_5134_, v___x_5135_);
return v___x_5136_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5139_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5140_ = lean_unsigned_to_nat(18u);
v___x_5141_ = lean_unsigned_to_nat(1962u);
v___x_5142_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5143_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5144_ = l_mkPanicMessageWithDecl(v___x_5143_, v___x_5142_, v___x_5141_, v___x_5140_, v___x_5139_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5145_, lean_object* v_newExpr_5146_){
_start:
{
if (lean_obj_tag(v_e_5145_) == 11)
{
lean_object* v_typeName_5147_; lean_object* v_idx_5148_; lean_object* v_struct_5149_; size_t v___x_5150_; size_t v___x_5151_; uint8_t v___x_5152_; 
v_typeName_5147_ = lean_ctor_get(v_e_5145_, 0);
v_idx_5148_ = lean_ctor_get(v_e_5145_, 1);
v_struct_5149_ = lean_ctor_get(v_e_5145_, 2);
v___x_5150_ = lean_ptr_addr(v_struct_5149_);
v___x_5151_ = lean_ptr_addr(v_newExpr_5146_);
v___x_5152_ = lean_usize_dec_eq(v___x_5150_, v___x_5151_);
if (v___x_5152_ == 0)
{
lean_object* v___x_5153_; 
lean_inc(v_idx_5148_);
lean_inc(v_typeName_5147_);
lean_dec_ref_known(v_e_5145_, 3);
v___x_5153_ = l_Lean_Expr_proj___override(v_typeName_5147_, v_idx_5148_, v_newExpr_5146_);
return v___x_5153_;
}
else
{
lean_dec_ref(v_newExpr_5146_);
return v_e_5145_;
}
}
else
{
lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
lean_dec_ref(v_newExpr_5146_);
lean_dec_ref(v_e_5145_);
v___x_5154_ = l_Lean_instInhabitedExpr;
v___x_5155_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5156_ = l_panic___redArg(v___x_5154_, v___x_5155_);
return v___x_5156_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; 
v___x_5159_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5160_ = lean_unsigned_to_nat(23u);
v___x_5161_ = lean_unsigned_to_nat(1977u);
v___x_5162_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5163_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5164_ = l_mkPanicMessageWithDecl(v___x_5163_, v___x_5162_, v___x_5161_, v___x_5160_, v___x_5159_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5165_, uint8_t v_newBinfo_5166_, lean_object* v_newDomain_5167_, lean_object* v_newBody_5168_){
_start:
{
if (lean_obj_tag(v_e_5165_) == 7)
{
lean_object* v_binderName_5169_; lean_object* v_binderType_5170_; lean_object* v_body_5171_; uint8_t v_binderInfo_5172_; size_t v___x_5173_; size_t v___x_5174_; uint8_t v___x_5175_; 
v_binderName_5169_ = lean_ctor_get(v_e_5165_, 0);
v_binderType_5170_ = lean_ctor_get(v_e_5165_, 1);
v_body_5171_ = lean_ctor_get(v_e_5165_, 2);
v_binderInfo_5172_ = lean_ctor_get_uint8(v_e_5165_, sizeof(void*)*3 + 8);
v___x_5173_ = lean_ptr_addr(v_binderType_5170_);
v___x_5174_ = lean_ptr_addr(v_newDomain_5167_);
v___x_5175_ = lean_usize_dec_eq(v___x_5173_, v___x_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; 
lean_inc(v_binderName_5169_);
lean_dec_ref_known(v_e_5165_, 3);
v___x_5176_ = l_Lean_Expr_forallE___override(v_binderName_5169_, v_newDomain_5167_, v_newBody_5168_, v_newBinfo_5166_);
return v___x_5176_;
}
else
{
size_t v___x_5177_; size_t v___x_5178_; uint8_t v___x_5179_; 
v___x_5177_ = lean_ptr_addr(v_body_5171_);
v___x_5178_ = lean_ptr_addr(v_newBody_5168_);
v___x_5179_ = lean_usize_dec_eq(v___x_5177_, v___x_5178_);
if (v___x_5179_ == 0)
{
lean_object* v___x_5180_; 
lean_inc(v_binderName_5169_);
lean_dec_ref_known(v_e_5165_, 3);
v___x_5180_ = l_Lean_Expr_forallE___override(v_binderName_5169_, v_newDomain_5167_, v_newBody_5168_, v_newBinfo_5166_);
return v___x_5180_;
}
else
{
uint8_t v___x_5181_; 
v___x_5181_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5172_, v_newBinfo_5166_);
if (v___x_5181_ == 0)
{
lean_object* v___x_5182_; 
lean_inc(v_binderName_5169_);
lean_dec_ref_known(v_e_5165_, 3);
v___x_5182_ = l_Lean_Expr_forallE___override(v_binderName_5169_, v_newDomain_5167_, v_newBody_5168_, v_newBinfo_5166_);
return v___x_5182_;
}
else
{
lean_dec_ref(v_newBody_5168_);
lean_dec_ref(v_newDomain_5167_);
return v_e_5165_;
}
}
}
}
else
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; 
lean_dec_ref(v_newBody_5168_);
lean_dec_ref(v_newDomain_5167_);
lean_dec_ref(v_e_5165_);
v___x_5183_ = l_Lean_instInhabitedExpr;
v___x_5184_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5185_ = l_panic___redArg(v___x_5183_, v___x_5184_);
return v___x_5185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5186_, lean_object* v_newBinfo_5187_, lean_object* v_newDomain_5188_, lean_object* v_newBody_5189_){
_start:
{
uint8_t v_newBinfo_boxed_5190_; lean_object* v_res_5191_; 
v_newBinfo_boxed_5190_ = lean_unbox(v_newBinfo_5187_);
v_res_5191_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5186_, v_newBinfo_boxed_5190_, v_newDomain_5188_, v_newBody_5189_);
return v_res_5191_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5193_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5194_ = lean_unsigned_to_nat(24u);
v___x_5195_ = lean_unsigned_to_nat(1988u);
v___x_5196_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5197_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5198_ = l_mkPanicMessageWithDecl(v___x_5197_, v___x_5196_, v___x_5195_, v___x_5194_, v___x_5193_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5199_, lean_object* v_newDomain_5200_, lean_object* v_newBody_5201_){
_start:
{
if (lean_obj_tag(v_e_5199_) == 7)
{
lean_object* v_binderName_5202_; lean_object* v_binderType_5203_; lean_object* v_body_5204_; uint8_t v_binderInfo_5205_; size_t v___x_5206_; size_t v___x_5207_; uint8_t v___x_5208_; 
v_binderName_5202_ = lean_ctor_get(v_e_5199_, 0);
v_binderType_5203_ = lean_ctor_get(v_e_5199_, 1);
v_body_5204_ = lean_ctor_get(v_e_5199_, 2);
v_binderInfo_5205_ = lean_ctor_get_uint8(v_e_5199_, sizeof(void*)*3 + 8);
v___x_5206_ = lean_ptr_addr(v_binderType_5203_);
v___x_5207_ = lean_ptr_addr(v_newDomain_5200_);
v___x_5208_ = lean_usize_dec_eq(v___x_5206_, v___x_5207_);
if (v___x_5208_ == 0)
{
lean_object* v___x_5209_; 
lean_inc(v_binderName_5202_);
lean_dec_ref_known(v_e_5199_, 3);
v___x_5209_ = l_Lean_Expr_forallE___override(v_binderName_5202_, v_newDomain_5200_, v_newBody_5201_, v_binderInfo_5205_);
return v___x_5209_;
}
else
{
size_t v___x_5210_; size_t v___x_5211_; uint8_t v___x_5212_; 
v___x_5210_ = lean_ptr_addr(v_body_5204_);
v___x_5211_ = lean_ptr_addr(v_newBody_5201_);
v___x_5212_ = lean_usize_dec_eq(v___x_5210_, v___x_5211_);
if (v___x_5212_ == 0)
{
lean_object* v___x_5213_; 
lean_inc(v_binderName_5202_);
lean_dec_ref_known(v_e_5199_, 3);
v___x_5213_ = l_Lean_Expr_forallE___override(v_binderName_5202_, v_newDomain_5200_, v_newBody_5201_, v_binderInfo_5205_);
return v___x_5213_;
}
else
{
uint8_t v___x_5214_; 
v___x_5214_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5205_, v_binderInfo_5205_);
if (v___x_5214_ == 0)
{
lean_object* v___x_5215_; 
lean_inc(v_binderName_5202_);
lean_dec_ref_known(v_e_5199_, 3);
v___x_5215_ = l_Lean_Expr_forallE___override(v_binderName_5202_, v_newDomain_5200_, v_newBody_5201_, v_binderInfo_5205_);
return v___x_5215_;
}
else
{
lean_dec_ref(v_newBody_5201_);
lean_dec_ref(v_newDomain_5200_);
return v_e_5199_;
}
}
}
}
else
{
lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; 
lean_dec_ref(v_newBody_5201_);
lean_dec_ref(v_newDomain_5200_);
lean_dec_ref(v_e_5199_);
v___x_5216_ = l_Lean_instInhabitedExpr;
v___x_5217_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5218_ = l_panic___redArg(v___x_5216_, v___x_5217_);
return v___x_5218_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5221_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5222_ = lean_unsigned_to_nat(19u);
v___x_5223_ = lean_unsigned_to_nat(1997u);
v___x_5224_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5225_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5226_ = l_mkPanicMessageWithDecl(v___x_5225_, v___x_5224_, v___x_5223_, v___x_5222_, v___x_5221_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5227_, uint8_t v_newBinfo_5228_, lean_object* v_newDomain_5229_, lean_object* v_newBody_5230_){
_start:
{
if (lean_obj_tag(v_e_5227_) == 6)
{
lean_object* v_binderName_5231_; lean_object* v_binderType_5232_; lean_object* v_body_5233_; uint8_t v_binderInfo_5234_; size_t v___x_5235_; size_t v___x_5236_; uint8_t v___x_5237_; 
v_binderName_5231_ = lean_ctor_get(v_e_5227_, 0);
v_binderType_5232_ = lean_ctor_get(v_e_5227_, 1);
v_body_5233_ = lean_ctor_get(v_e_5227_, 2);
v_binderInfo_5234_ = lean_ctor_get_uint8(v_e_5227_, sizeof(void*)*3 + 8);
v___x_5235_ = lean_ptr_addr(v_binderType_5232_);
v___x_5236_ = lean_ptr_addr(v_newDomain_5229_);
v___x_5237_ = lean_usize_dec_eq(v___x_5235_, v___x_5236_);
if (v___x_5237_ == 0)
{
lean_object* v___x_5238_; 
lean_inc(v_binderName_5231_);
lean_dec_ref_known(v_e_5227_, 3);
v___x_5238_ = l_Lean_Expr_lam___override(v_binderName_5231_, v_newDomain_5229_, v_newBody_5230_, v_newBinfo_5228_);
return v___x_5238_;
}
else
{
size_t v___x_5239_; size_t v___x_5240_; uint8_t v___x_5241_; 
v___x_5239_ = lean_ptr_addr(v_body_5233_);
v___x_5240_ = lean_ptr_addr(v_newBody_5230_);
v___x_5241_ = lean_usize_dec_eq(v___x_5239_, v___x_5240_);
if (v___x_5241_ == 0)
{
lean_object* v___x_5242_; 
lean_inc(v_binderName_5231_);
lean_dec_ref_known(v_e_5227_, 3);
v___x_5242_ = l_Lean_Expr_lam___override(v_binderName_5231_, v_newDomain_5229_, v_newBody_5230_, v_newBinfo_5228_);
return v___x_5242_;
}
else
{
uint8_t v___x_5243_; 
v___x_5243_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5234_, v_newBinfo_5228_);
if (v___x_5243_ == 0)
{
lean_object* v___x_5244_; 
lean_inc(v_binderName_5231_);
lean_dec_ref_known(v_e_5227_, 3);
v___x_5244_ = l_Lean_Expr_lam___override(v_binderName_5231_, v_newDomain_5229_, v_newBody_5230_, v_newBinfo_5228_);
return v___x_5244_;
}
else
{
lean_dec_ref(v_newBody_5230_);
lean_dec_ref(v_newDomain_5229_);
return v_e_5227_;
}
}
}
}
else
{
lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
lean_dec_ref(v_newBody_5230_);
lean_dec_ref(v_newDomain_5229_);
lean_dec_ref(v_e_5227_);
v___x_5245_ = l_Lean_instInhabitedExpr;
v___x_5246_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5247_ = l_panic___redArg(v___x_5245_, v___x_5246_);
return v___x_5247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5248_, lean_object* v_newBinfo_5249_, lean_object* v_newDomain_5250_, lean_object* v_newBody_5251_){
_start:
{
uint8_t v_newBinfo_boxed_5252_; lean_object* v_res_5253_; 
v_newBinfo_boxed_5252_ = lean_unbox(v_newBinfo_5249_);
v_res_5253_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5248_, v_newBinfo_boxed_5252_, v_newDomain_5250_, v_newBody_5251_);
return v_res_5253_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5255_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5256_ = lean_unsigned_to_nat(20u);
v___x_5257_ = lean_unsigned_to_nat(2008u);
v___x_5258_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5259_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5260_ = l_mkPanicMessageWithDecl(v___x_5259_, v___x_5258_, v___x_5257_, v___x_5256_, v___x_5255_);
return v___x_5260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5261_, lean_object* v_newDomain_5262_, lean_object* v_newBody_5263_){
_start:
{
if (lean_obj_tag(v_e_5261_) == 6)
{
lean_object* v_binderName_5264_; lean_object* v_binderType_5265_; lean_object* v_body_5266_; uint8_t v_binderInfo_5267_; size_t v___x_5268_; size_t v___x_5269_; uint8_t v___x_5270_; 
v_binderName_5264_ = lean_ctor_get(v_e_5261_, 0);
v_binderType_5265_ = lean_ctor_get(v_e_5261_, 1);
v_body_5266_ = lean_ctor_get(v_e_5261_, 2);
v_binderInfo_5267_ = lean_ctor_get_uint8(v_e_5261_, sizeof(void*)*3 + 8);
v___x_5268_ = lean_ptr_addr(v_binderType_5265_);
v___x_5269_ = lean_ptr_addr(v_newDomain_5262_);
v___x_5270_ = lean_usize_dec_eq(v___x_5268_, v___x_5269_);
if (v___x_5270_ == 0)
{
lean_object* v___x_5271_; 
lean_inc(v_binderName_5264_);
lean_dec_ref_known(v_e_5261_, 3);
v___x_5271_ = l_Lean_Expr_lam___override(v_binderName_5264_, v_newDomain_5262_, v_newBody_5263_, v_binderInfo_5267_);
return v___x_5271_;
}
else
{
size_t v___x_5272_; size_t v___x_5273_; uint8_t v___x_5274_; 
v___x_5272_ = lean_ptr_addr(v_body_5266_);
v___x_5273_ = lean_ptr_addr(v_newBody_5263_);
v___x_5274_ = lean_usize_dec_eq(v___x_5272_, v___x_5273_);
if (v___x_5274_ == 0)
{
lean_object* v___x_5275_; 
lean_inc(v_binderName_5264_);
lean_dec_ref_known(v_e_5261_, 3);
v___x_5275_ = l_Lean_Expr_lam___override(v_binderName_5264_, v_newDomain_5262_, v_newBody_5263_, v_binderInfo_5267_);
return v___x_5275_;
}
else
{
uint8_t v___x_5276_; 
v___x_5276_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5267_, v_binderInfo_5267_);
if (v___x_5276_ == 0)
{
lean_object* v___x_5277_; 
lean_inc(v_binderName_5264_);
lean_dec_ref_known(v_e_5261_, 3);
v___x_5277_ = l_Lean_Expr_lam___override(v_binderName_5264_, v_newDomain_5262_, v_newBody_5263_, v_binderInfo_5267_);
return v___x_5277_;
}
else
{
lean_dec_ref(v_newBody_5263_);
lean_dec_ref(v_newDomain_5262_);
return v_e_5261_;
}
}
}
}
else
{
lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
lean_dec_ref(v_newBody_5263_);
lean_dec_ref(v_newDomain_5262_);
lean_dec_ref(v_e_5261_);
v___x_5278_ = l_Lean_instInhabitedExpr;
v___x_5279_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5280_ = l_panic___redArg(v___x_5278_, v___x_5279_);
return v___x_5280_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; 
v___x_5282_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5283_ = lean_unsigned_to_nat(22u);
v___x_5284_ = lean_unsigned_to_nat(2017u);
v___x_5285_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5286_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5287_ = l_mkPanicMessageWithDecl(v___x_5286_, v___x_5285_, v___x_5284_, v___x_5283_, v___x_5282_);
return v___x_5287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5288_, lean_object* v_newType_5289_, lean_object* v_newVal_5290_, lean_object* v_newBody_5291_, uint8_t v_newNondep_5292_){
_start:
{
if (lean_obj_tag(v_e_5288_) == 8)
{
lean_object* v_declName_5293_; lean_object* v_type_5294_; lean_object* v_value_5295_; lean_object* v_body_5296_; uint8_t v_nondep_5297_; size_t v___x_5298_; size_t v___x_5299_; uint8_t v___x_5300_; 
v_declName_5293_ = lean_ctor_get(v_e_5288_, 0);
v_type_5294_ = lean_ctor_get(v_e_5288_, 1);
v_value_5295_ = lean_ctor_get(v_e_5288_, 2);
v_body_5296_ = lean_ctor_get(v_e_5288_, 3);
v_nondep_5297_ = lean_ctor_get_uint8(v_e_5288_, sizeof(void*)*4 + 8);
v___x_5298_ = lean_ptr_addr(v_type_5294_);
v___x_5299_ = lean_ptr_addr(v_newType_5289_);
v___x_5300_ = lean_usize_dec_eq(v___x_5298_, v___x_5299_);
if (v___x_5300_ == 0)
{
lean_object* v___x_5301_; 
lean_inc(v_declName_5293_);
lean_dec_ref_known(v_e_5288_, 4);
v___x_5301_ = l_Lean_Expr_letE___override(v_declName_5293_, v_newType_5289_, v_newVal_5290_, v_newBody_5291_, v_newNondep_5292_);
return v___x_5301_;
}
else
{
size_t v___x_5302_; size_t v___x_5303_; uint8_t v___x_5304_; 
v___x_5302_ = lean_ptr_addr(v_value_5295_);
v___x_5303_ = lean_ptr_addr(v_newVal_5290_);
v___x_5304_ = lean_usize_dec_eq(v___x_5302_, v___x_5303_);
if (v___x_5304_ == 0)
{
lean_object* v___x_5305_; 
lean_inc(v_declName_5293_);
lean_dec_ref_known(v_e_5288_, 4);
v___x_5305_ = l_Lean_Expr_letE___override(v_declName_5293_, v_newType_5289_, v_newVal_5290_, v_newBody_5291_, v_newNondep_5292_);
return v___x_5305_;
}
else
{
size_t v___x_5306_; size_t v___x_5307_; uint8_t v___x_5308_; 
v___x_5306_ = lean_ptr_addr(v_body_5296_);
v___x_5307_ = lean_ptr_addr(v_newBody_5291_);
v___x_5308_ = lean_usize_dec_eq(v___x_5306_, v___x_5307_);
if (v___x_5308_ == 0)
{
lean_object* v___x_5309_; 
lean_inc(v_declName_5293_);
lean_dec_ref_known(v_e_5288_, 4);
v___x_5309_ = l_Lean_Expr_letE___override(v_declName_5293_, v_newType_5289_, v_newVal_5290_, v_newBody_5291_, v_newNondep_5292_);
return v___x_5309_;
}
else
{
if (v_newNondep_5292_ == 0)
{
if (v_nondep_5297_ == 0)
{
lean_dec_ref(v_newBody_5291_);
lean_dec_ref(v_newVal_5290_);
lean_dec_ref(v_newType_5289_);
return v_e_5288_;
}
else
{
lean_object* v___x_5310_; 
lean_inc(v_declName_5293_);
lean_dec_ref_known(v_e_5288_, 4);
v___x_5310_ = l_Lean_Expr_letE___override(v_declName_5293_, v_newType_5289_, v_newVal_5290_, v_newBody_5291_, v_newNondep_5292_);
return v___x_5310_;
}
}
else
{
if (v_nondep_5297_ == 0)
{
lean_object* v___x_5311_; 
lean_inc(v_declName_5293_);
lean_dec_ref_known(v_e_5288_, 4);
v___x_5311_ = l_Lean_Expr_letE___override(v_declName_5293_, v_newType_5289_, v_newVal_5290_, v_newBody_5291_, v_newNondep_5292_);
return v___x_5311_;
}
else
{
lean_dec_ref(v_newBody_5291_);
lean_dec_ref(v_newVal_5290_);
lean_dec_ref(v_newType_5289_);
return v_e_5288_;
}
}
}
}
}
}
else
{
lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; 
lean_dec_ref(v_newBody_5291_);
lean_dec_ref(v_newVal_5290_);
lean_dec_ref(v_newType_5289_);
lean_dec_ref(v_e_5288_);
v___x_5312_ = l_Lean_instInhabitedExpr;
v___x_5313_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5314_ = l_panic___redArg(v___x_5312_, v___x_5313_);
return v___x_5314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5315_, lean_object* v_newType_5316_, lean_object* v_newVal_5317_, lean_object* v_newBody_5318_, lean_object* v_newNondep_5319_){
_start:
{
uint8_t v_newNondep_boxed_5320_; lean_object* v_res_5321_; 
v_newNondep_boxed_5320_ = lean_unbox(v_newNondep_5319_);
v_res_5321_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5315_, v_newType_5316_, v_newVal_5317_, v_newBody_5318_, v_newNondep_boxed_5320_);
return v_res_5321_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
v___x_5323_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5324_ = lean_unsigned_to_nat(27u);
v___x_5325_ = lean_unsigned_to_nat(2030u);
v___x_5326_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5327_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5328_ = l_mkPanicMessageWithDecl(v___x_5327_, v___x_5326_, v___x_5325_, v___x_5324_, v___x_5323_);
return v___x_5328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5329_, lean_object* v_newType_5330_, lean_object* v_newVal_5331_, lean_object* v_newBody_5332_){
_start:
{
if (lean_obj_tag(v_e_5329_) == 8)
{
lean_object* v_declName_5333_; lean_object* v_type_5334_; lean_object* v_value_5335_; lean_object* v_body_5336_; uint8_t v_nondep_5337_; size_t v___x_5338_; size_t v___x_5339_; uint8_t v___x_5340_; 
v_declName_5333_ = lean_ctor_get(v_e_5329_, 0);
v_type_5334_ = lean_ctor_get(v_e_5329_, 1);
v_value_5335_ = lean_ctor_get(v_e_5329_, 2);
v_body_5336_ = lean_ctor_get(v_e_5329_, 3);
v_nondep_5337_ = lean_ctor_get_uint8(v_e_5329_, sizeof(void*)*4 + 8);
v___x_5338_ = lean_ptr_addr(v_type_5334_);
v___x_5339_ = lean_ptr_addr(v_newType_5330_);
v___x_5340_ = lean_usize_dec_eq(v___x_5338_, v___x_5339_);
if (v___x_5340_ == 0)
{
lean_object* v___x_5341_; 
lean_inc(v_declName_5333_);
lean_dec_ref_known(v_e_5329_, 4);
v___x_5341_ = l_Lean_Expr_letE___override(v_declName_5333_, v_newType_5330_, v_newVal_5331_, v_newBody_5332_, v_nondep_5337_);
return v___x_5341_;
}
else
{
size_t v___x_5342_; size_t v___x_5343_; uint8_t v___x_5344_; 
v___x_5342_ = lean_ptr_addr(v_value_5335_);
v___x_5343_ = lean_ptr_addr(v_newVal_5331_);
v___x_5344_ = lean_usize_dec_eq(v___x_5342_, v___x_5343_);
if (v___x_5344_ == 0)
{
lean_object* v___x_5345_; 
lean_inc(v_declName_5333_);
lean_dec_ref_known(v_e_5329_, 4);
v___x_5345_ = l_Lean_Expr_letE___override(v_declName_5333_, v_newType_5330_, v_newVal_5331_, v_newBody_5332_, v_nondep_5337_);
return v___x_5345_;
}
else
{
size_t v___x_5346_; size_t v___x_5347_; uint8_t v___x_5348_; 
v___x_5346_ = lean_ptr_addr(v_body_5336_);
v___x_5347_ = lean_ptr_addr(v_newBody_5332_);
v___x_5348_ = lean_usize_dec_eq(v___x_5346_, v___x_5347_);
if (v___x_5348_ == 0)
{
lean_object* v___x_5349_; 
lean_inc(v_declName_5333_);
lean_dec_ref_known(v_e_5329_, 4);
v___x_5349_ = l_Lean_Expr_letE___override(v_declName_5333_, v_newType_5330_, v_newVal_5331_, v_newBody_5332_, v_nondep_5337_);
return v___x_5349_;
}
else
{
lean_dec_ref(v_newBody_5332_);
lean_dec_ref(v_newVal_5331_);
lean_dec_ref(v_newType_5330_);
return v_e_5329_;
}
}
}
}
else
{
lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; 
lean_dec_ref(v_newBody_5332_);
lean_dec_ref(v_newVal_5331_);
lean_dec_ref(v_newType_5330_);
lean_dec_ref(v_e_5329_);
v___x_5350_ = l_Lean_instInhabitedExpr;
v___x_5351_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5352_ = l_panic___redArg(v___x_5350_, v___x_5351_);
return v___x_5352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5353_, lean_object* v_x_5354_){
_start:
{
if (lean_obj_tag(v_x_5353_) == 5)
{
lean_object* v_fn_5355_; lean_object* v_arg_5356_; lean_object* v___x_5357_; size_t v___x_5358_; size_t v___x_5359_; uint8_t v___x_5360_; 
v_fn_5355_ = lean_ctor_get(v_x_5353_, 0);
v_arg_5356_ = lean_ctor_get(v_x_5353_, 1);
lean_inc_ref(v_fn_5355_);
v___x_5357_ = l_Lean_Expr_updateFn(v_fn_5355_, v_x_5354_);
v___x_5358_ = lean_ptr_addr(v_fn_5355_);
v___x_5359_ = lean_ptr_addr(v___x_5357_);
v___x_5360_ = lean_usize_dec_eq(v___x_5358_, v___x_5359_);
if (v___x_5360_ == 0)
{
lean_object* v___x_5361_; 
lean_inc_ref(v_arg_5356_);
lean_dec_ref_known(v_x_5353_, 2);
v___x_5361_ = l_Lean_Expr_app___override(v___x_5357_, v_arg_5356_);
return v___x_5361_;
}
else
{
size_t v___x_5362_; size_t v___x_5363_; uint8_t v___x_5364_; 
v___x_5362_ = lean_ptr_addr(v_arg_5356_);
v___x_5363_ = lean_ptr_addr(v_arg_5356_);
v___x_5364_ = lean_usize_dec_eq(v___x_5362_, v___x_5363_);
if (v___x_5364_ == 0)
{
lean_object* v___x_5365_; 
lean_inc_ref(v_arg_5356_);
lean_dec_ref_known(v_x_5353_, 2);
v___x_5365_ = l_Lean_Expr_app___override(v___x_5357_, v_arg_5356_);
return v___x_5365_;
}
else
{
lean_dec_ref(v___x_5357_);
return v_x_5353_;
}
}
}
else
{
lean_dec_ref(v_x_5353_);
lean_inc_ref(v_x_5354_);
return v_x_5354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5366_, lean_object* v_x_5367_){
_start:
{
lean_object* v_res_5368_; 
v_res_5368_ = l_Lean_Expr_updateFn(v_x_5366_, v_x_5367_);
lean_dec_ref(v_x_5367_);
return v_res_5368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateAppN_go(lean_object* v_newFn_5369_, lean_object* v_newArgs_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_){
_start:
{
lean_object* v_i_5374_; 
if (lean_obj_tag(v_a_5371_) == 5)
{
lean_object* v_fn_5377_; lean_object* v_arg_5378_; lean_object* v_zero_5379_; uint8_t v_isZero_5380_; 
v_fn_5377_ = lean_ctor_get(v_a_5371_, 0);
v_arg_5378_ = lean_ctor_get(v_a_5371_, 1);
v_zero_5379_ = lean_unsigned_to_nat(0u);
v_isZero_5380_ = lean_nat_dec_eq(v_a_5372_, v_zero_5379_);
if (v_isZero_5380_ == 0)
{
lean_object* v___x_5381_; lean_object* v_one_5382_; lean_object* v_n_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; size_t v___x_5386_; size_t v___x_5387_; uint8_t v___x_5388_; 
v___x_5381_ = l_Lean_instInhabitedExpr;
v_one_5382_ = lean_unsigned_to_nat(1u);
v_n_5383_ = lean_nat_sub(v_a_5372_, v_one_5382_);
v___x_5384_ = l___private_Lean_Expr_0__Lean_Expr_updateAppN_go(v_newFn_5369_, v_newArgs_5370_, v_fn_5377_, v_n_5383_);
v___x_5385_ = lean_array_get_borrowed(v___x_5381_, v_newArgs_5370_, v_n_5383_);
lean_dec(v_n_5383_);
v___x_5386_ = lean_ptr_addr(v_fn_5377_);
v___x_5387_ = lean_ptr_addr(v___x_5384_);
v___x_5388_ = lean_usize_dec_eq(v___x_5386_, v___x_5387_);
if (v___x_5388_ == 0)
{
lean_object* v___x_5389_; 
lean_inc(v___x_5385_);
v___x_5389_ = l_Lean_Expr_app___override(v___x_5384_, v___x_5385_);
return v___x_5389_;
}
else
{
size_t v___x_5390_; size_t v___x_5391_; uint8_t v___x_5392_; 
v___x_5390_ = lean_ptr_addr(v_arg_5378_);
v___x_5391_ = lean_ptr_addr(v___x_5385_);
v___x_5392_ = lean_usize_dec_eq(v___x_5390_, v___x_5391_);
if (v___x_5392_ == 0)
{
lean_object* v___x_5393_; 
lean_inc(v___x_5385_);
v___x_5393_ = l_Lean_Expr_app___override(v___x_5384_, v___x_5385_);
return v___x_5393_;
}
else
{
lean_dec_ref(v___x_5384_);
lean_inc_ref(v_a_5371_);
return v_a_5371_;
}
}
}
else
{
v_i_5374_ = v_a_5372_;
goto v___jp_5373_;
}
}
else
{
v_i_5374_ = v_a_5372_;
goto v___jp_5373_;
}
v___jp_5373_:
{
lean_object* v___x_5375_; lean_object* v___x_5376_; 
v___x_5375_ = lean_unsigned_to_nat(0u);
v___x_5376_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_i_5374_, v_newArgs_5370_, v___x_5375_, v_newFn_5369_);
return v___x_5376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateAppN_go___boxed(lean_object* v_newFn_5394_, lean_object* v_newArgs_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_){
_start:
{
lean_object* v_res_5398_; 
v_res_5398_ = l___private_Lean_Expr_0__Lean_Expr_updateAppN_go(v_newFn_5394_, v_newArgs_5395_, v_a_5396_, v_a_5397_);
lean_dec(v_a_5397_);
lean_dec_ref(v_a_5396_);
lean_dec_ref(v_newArgs_5395_);
return v_res_5398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppN(lean_object* v_e_5399_, lean_object* v_newFn_5400_, lean_object* v_newArgs_5401_){
_start:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5402_ = lean_array_get_size(v_newArgs_5401_);
v___x_5403_ = l___private_Lean_Expr_0__Lean_Expr_updateAppN_go(v_newFn_5400_, v_newArgs_5401_, v_e_5399_, v___x_5402_);
return v___x_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppN___boxed(lean_object* v_e_5404_, lean_object* v_newFn_5405_, lean_object* v_newArgs_5406_){
_start:
{
lean_object* v_res_5407_; 
v_res_5407_ = l_Lean_Expr_updateAppN(v_e_5404_, v_newFn_5405_, v_newArgs_5406_);
lean_dec_ref(v_newArgs_5406_);
lean_dec_ref(v_e_5404_);
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mapAppN___redArg___lam__0(lean_object* v_e_5408_, lean_object* v_toPure_5409_, lean_object* v_____x_5410_){
_start:
{
lean_object* v_fst_5411_; lean_object* v_snd_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; 
v_fst_5411_ = lean_ctor_get(v_____x_5410_, 0);
lean_inc(v_fst_5411_);
v_snd_5412_ = lean_ctor_get(v_____x_5410_, 1);
lean_inc(v_snd_5412_);
lean_dec_ref(v_____x_5410_);
v___x_5413_ = l_Lean_Expr_updateAppN(v_e_5408_, v_fst_5411_, v_snd_5412_);
lean_dec(v_snd_5412_);
v___x_5414_ = lean_apply_2(v_toPure_5409_, lean_box(0), v___x_5413_);
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mapAppN___redArg___lam__0___boxed(lean_object* v_e_5415_, lean_object* v_toPure_5416_, lean_object* v_____x_5417_){
_start:
{
lean_object* v_res_5418_; 
v_res_5418_ = l_Lean_Expr_mapAppN___redArg___lam__0(v_e_5415_, v_toPure_5416_, v_____x_5417_);
lean_dec_ref(v_e_5415_);
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mapAppN___redArg___lam__1(lean_object* v_k_5419_, lean_object* v_toBind_5420_, lean_object* v___f_5421_, lean_object* v_f_5422_, lean_object* v_args_5423_){
_start:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5424_ = lean_apply_2(v_k_5419_, v_f_5422_, v_args_5423_);
v___x_5425_ = lean_apply_4(v_toBind_5420_, lean_box(0), lean_box(0), v___x_5424_, v___f_5421_);
return v___x_5425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mapAppN___redArg(lean_object* v_inst_5426_, lean_object* v_e_5427_, lean_object* v_k_5428_){
_start:
{
lean_object* v_toApplicative_5429_; lean_object* v_toBind_5430_; lean_object* v_toPure_5431_; lean_object* v___f_5432_; lean_object* v___f_5433_; lean_object* v_dummy_5434_; lean_object* v_nargs_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
v_toApplicative_5429_ = lean_ctor_get(v_inst_5426_, 0);
lean_inc_ref(v_toApplicative_5429_);
v_toBind_5430_ = lean_ctor_get(v_inst_5426_, 1);
lean_inc(v_toBind_5430_);
lean_dec_ref(v_inst_5426_);
v_toPure_5431_ = lean_ctor_get(v_toApplicative_5429_, 1);
lean_inc(v_toPure_5431_);
lean_dec_ref(v_toApplicative_5429_);
lean_inc_ref(v_e_5427_);
v___f_5432_ = lean_alloc_closure((void*)(l_Lean_Expr_mapAppN___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_5432_, 0, v_e_5427_);
lean_closure_set(v___f_5432_, 1, v_toPure_5431_);
v___f_5433_ = lean_alloc_closure((void*)(l_Lean_Expr_mapAppN___redArg___lam__1), 5, 3);
lean_closure_set(v___f_5433_, 0, v_k_5428_);
lean_closure_set(v___f_5433_, 1, v_toBind_5430_);
lean_closure_set(v___f_5433_, 2, v___f_5432_);
v_dummy_5434_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5435_ = l_Lean_Expr_getAppNumArgs(v_e_5427_);
lean_inc(v_nargs_5435_);
v___x_5436_ = lean_mk_array(v_nargs_5435_, v_dummy_5434_);
v___x_5437_ = lean_unsigned_to_nat(1u);
v___x_5438_ = lean_nat_sub(v_nargs_5435_, v___x_5437_);
lean_dec(v_nargs_5435_);
v___x_5439_ = l_Lean_Expr_withAppAux___redArg(v___f_5433_, v_e_5427_, v___x_5436_, v___x_5438_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mapAppN(lean_object* v_m_5440_, lean_object* v_inst_5441_, lean_object* v_e_5442_, lean_object* v_k_5443_){
_start:
{
lean_object* v_toApplicative_5444_; lean_object* v_toBind_5445_; lean_object* v_toPure_5446_; lean_object* v___f_5447_; lean_object* v___f_5448_; lean_object* v_dummy_5449_; lean_object* v_nargs_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; 
v_toApplicative_5444_ = lean_ctor_get(v_inst_5441_, 0);
lean_inc_ref(v_toApplicative_5444_);
v_toBind_5445_ = lean_ctor_get(v_inst_5441_, 1);
lean_inc(v_toBind_5445_);
lean_dec_ref(v_inst_5441_);
v_toPure_5446_ = lean_ctor_get(v_toApplicative_5444_, 1);
lean_inc(v_toPure_5446_);
lean_dec_ref(v_toApplicative_5444_);
lean_inc_ref(v_e_5442_);
v___f_5447_ = lean_alloc_closure((void*)(l_Lean_Expr_mapAppN___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_5447_, 0, v_e_5442_);
lean_closure_set(v___f_5447_, 1, v_toPure_5446_);
v___f_5448_ = lean_alloc_closure((void*)(l_Lean_Expr_mapAppN___redArg___lam__1), 5, 3);
lean_closure_set(v___f_5448_, 0, v_k_5443_);
lean_closure_set(v___f_5448_, 1, v_toBind_5445_);
lean_closure_set(v___f_5448_, 2, v___f_5447_);
v_dummy_5449_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5450_ = l_Lean_Expr_getAppNumArgs(v_e_5442_);
lean_inc(v_nargs_5450_);
v___x_5451_ = lean_mk_array(v_nargs_5450_, v_dummy_5449_);
v___x_5452_ = lean_unsigned_to_nat(1u);
v___x_5453_ = lean_nat_sub(v_nargs_5450_, v___x_5452_);
lean_dec(v_nargs_5450_);
v___x_5454_ = l_Lean_Expr_withAppAux___redArg(v___f_5448_, v_e_5442_, v___x_5451_, v___x_5453_);
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5455_){
_start:
{
if (lean_obj_tag(v_e_5455_) == 6)
{
lean_object* v_binderName_5456_; lean_object* v_binderType_5457_; lean_object* v_body_5458_; uint8_t v_binderInfo_5459_; lean_object* v_b_x27_5460_; 
v_binderName_5456_ = lean_ctor_get(v_e_5455_, 0);
v_binderType_5457_ = lean_ctor_get(v_e_5455_, 1);
v_body_5458_ = lean_ctor_get(v_e_5455_, 2);
v_binderInfo_5459_ = lean_ctor_get_uint8(v_e_5455_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5458_);
v_b_x27_5460_ = l_Lean_Expr_eta(v_body_5458_);
if (lean_obj_tag(v_b_x27_5460_) == 5)
{
lean_object* v_arg_5472_; 
v_arg_5472_ = lean_ctor_get(v_b_x27_5460_, 1);
if (lean_obj_tag(v_arg_5472_) == 0)
{
lean_object* v_fn_5473_; lean_object* v_deBruijnIndex_5474_; lean_object* v___x_5475_; uint8_t v___x_5476_; 
v_fn_5473_ = lean_ctor_get(v_b_x27_5460_, 0);
v_deBruijnIndex_5474_ = lean_ctor_get(v_arg_5472_, 0);
v___x_5475_ = lean_unsigned_to_nat(0u);
v___x_5476_ = lean_nat_dec_eq(v_deBruijnIndex_5474_, v___x_5475_);
if (v___x_5476_ == 0)
{
goto v___jp_5461_;
}
else
{
uint8_t v___x_5477_; 
v___x_5477_ = lean_expr_has_loose_bvar(v_fn_5473_, v___x_5475_);
if (v___x_5477_ == 0)
{
lean_object* v___x_5478_; lean_object* v___x_5479_; 
lean_inc_ref(v_fn_5473_);
lean_dec_ref_known(v_b_x27_5460_, 2);
lean_dec_ref_known(v_e_5455_, 3);
v___x_5478_ = lean_unsigned_to_nat(1u);
v___x_5479_ = lean_expr_lower_loose_bvars(v_fn_5473_, v___x_5478_, v___x_5478_);
lean_dec_ref(v_fn_5473_);
return v___x_5479_;
}
else
{
size_t v___x_5480_; size_t v___x_5481_; uint8_t v___x_5482_; 
v___x_5480_ = lean_ptr_addr(v_binderType_5457_);
v___x_5481_ = lean_ptr_addr(v_binderType_5457_);
v___x_5482_ = lean_usize_dec_eq(v___x_5480_, v___x_5481_);
if (v___x_5482_ == 0)
{
lean_object* v___x_5483_; 
lean_inc_ref(v_binderType_5457_);
lean_inc(v_binderName_5456_);
lean_dec_ref_known(v_e_5455_, 3);
v___x_5483_ = l_Lean_Expr_lam___override(v_binderName_5456_, v_binderType_5457_, v_b_x27_5460_, v_binderInfo_5459_);
return v___x_5483_;
}
else
{
size_t v___x_5484_; size_t v___x_5485_; uint8_t v___x_5486_; 
v___x_5484_ = lean_ptr_addr(v_body_5458_);
v___x_5485_ = lean_ptr_addr(v_b_x27_5460_);
v___x_5486_ = lean_usize_dec_eq(v___x_5484_, v___x_5485_);
if (v___x_5486_ == 0)
{
lean_object* v___x_5487_; 
lean_inc_ref(v_binderType_5457_);
lean_inc(v_binderName_5456_);
lean_dec_ref_known(v_e_5455_, 3);
v___x_5487_ = l_Lean_Expr_lam___override(v_binderName_5456_, v_binderType_5457_, v_b_x27_5460_, v_binderInfo_5459_);
return v___x_5487_;
}
else
{
uint8_t v___x_5488_; 
v___x_5488_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5459_, v_binderInfo_5459_);
if (v___x_5488_ == 0)
{
lean_object* v___x_5489_; 
lean_inc_ref(v_binderType_5457_);
lean_inc(v_binderName_5456_);
lean_dec_ref_known(v_e_5455_, 3);
v___x_5489_ = l_Lean_Expr_lam___override(v_binderName_5456_, v_binderType_5457_, v_b_x27_5460_, v_binderInfo_5459_);
return v___x_5489_;
}
else
{
lean_dec_ref_known(v_b_x27_5460_, 2);
return v_e_5455_;
}
}
}
}
}
}
else
{
goto v___jp_5461_;
}
}
else
{
goto v___jp_5461_;
}
v___jp_5461_:
{
size_t v___x_5462_; size_t v___x_5463_; uint8_t v___x_5464_; 
v___x_5462_ = lean_ptr_addr(v_binderType_5457_);
v___x_5463_ = lean_ptr_addr(v_binderType_5457_);
v___x_5464_ = lean_usize_dec_eq(v___x_5462_, v___x_5463_);
if (v___x_5464_ == 0)
{
lean_object* v___x_5465_; 
lean_inc_ref(v_binderType_5457_);
lean_inc(v_binderName_5456_);
lean_dec_ref_known(v_e_5455_, 3);
v___x_5465_ = l_Lean_Expr_lam___override(v_binderName_5456_, v_binderType_5457_, v_b_x27_5460_, v_binderInfo_5459_);
return v___x_5465_;
}
else
{
size_t v___x_5466_; size_t v___x_5467_; uint8_t v___x_5468_; 
v___x_5466_ = lean_ptr_addr(v_body_5458_);
v___x_5467_ = lean_ptr_addr(v_b_x27_5460_);
v___x_5468_ = lean_usize_dec_eq(v___x_5466_, v___x_5467_);
if (v___x_5468_ == 0)
{
lean_object* v___x_5469_; 
lean_inc_ref(v_binderType_5457_);
lean_inc(v_binderName_5456_);
lean_dec_ref_known(v_e_5455_, 3);
v___x_5469_ = l_Lean_Expr_lam___override(v_binderName_5456_, v_binderType_5457_, v_b_x27_5460_, v_binderInfo_5459_);
return v___x_5469_;
}
else
{
uint8_t v___x_5470_; 
v___x_5470_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5459_, v_binderInfo_5459_);
if (v___x_5470_ == 0)
{
lean_object* v___x_5471_; 
lean_inc_ref(v_binderType_5457_);
lean_inc(v_binderName_5456_);
lean_dec_ref_known(v_e_5455_, 3);
v___x_5471_ = l_Lean_Expr_lam___override(v_binderName_5456_, v_binderType_5457_, v_b_x27_5460_, v_binderInfo_5459_);
return v___x_5471_;
}
else
{
lean_dec_ref(v_b_x27_5460_);
return v_e_5455_;
}
}
}
}
}
else
{
return v_e_5455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5490_, lean_object* v_optionName_5491_, lean_object* v_inst_5492_, lean_object* v_val_5493_){
_start:
{
lean_object* v_toDataValue_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
v_toDataValue_5494_ = lean_ctor_get(v_inst_5492_, 0);
lean_inc_ref(v_toDataValue_5494_);
lean_dec_ref(v_inst_5492_);
v___x_5495_ = lean_box(0);
v___x_5496_ = lean_apply_1(v_toDataValue_5494_, v_val_5493_);
v___x_5497_ = l_Lean_KVMap_insert(v___x_5495_, v_optionName_5491_, v___x_5496_);
v___x_5498_ = l_Lean_Expr_mdata___override(v___x_5497_, v_e_5490_);
return v___x_5498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5499_, lean_object* v_e_5500_, lean_object* v_optionName_5501_, lean_object* v_inst_5502_, lean_object* v_val_5503_){
_start:
{
lean_object* v___x_5504_; 
v___x_5504_ = l_Lean_Expr_setOption___redArg(v_e_5500_, v_optionName_5501_, v_inst_5502_, v_val_5503_);
return v___x_5504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5505_, lean_object* v_optionName_5506_, uint8_t v_val_5507_){
_start:
{
lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5508_ = lean_box(0);
v___x_5509_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5509_, 0, v_val_5507_);
v___x_5510_ = l_Lean_KVMap_insert(v___x_5508_, v_optionName_5506_, v___x_5509_);
v___x_5511_ = l_Lean_Expr_mdata___override(v___x_5510_, v_e_5505_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5512_, lean_object* v_optionName_5513_, lean_object* v_val_5514_){
_start:
{
uint8_t v_val_boxed_5515_; lean_object* v_res_5516_; 
v_val_boxed_5515_ = lean_unbox(v_val_5514_);
v_res_5516_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5512_, v_optionName_5513_, v_val_boxed_5515_);
return v_res_5516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5522_, uint8_t v_flag_5523_){
_start:
{
lean_object* v___x_5524_; lean_object* v___x_5525_; 
v___x_5524_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5525_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5522_, v___x_5524_, v_flag_5523_);
return v___x_5525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5526_, lean_object* v_flag_5527_){
_start:
{
uint8_t v_flag_boxed_5528_; lean_object* v_res_5529_; 
v_flag_boxed_5528_ = lean_unbox(v_flag_5527_);
v_res_5529_ = l_Lean_Expr_setPPExplicit(v_e_5526_, v_flag_boxed_5528_);
return v_res_5529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5534_, uint8_t v_flag_5535_){
_start:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
v___x_5536_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5537_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5534_, v___x_5536_, v_flag_5535_);
return v___x_5537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5538_, lean_object* v_flag_5539_){
_start:
{
uint8_t v_flag_boxed_5540_; lean_object* v_res_5541_; 
v_flag_boxed_5540_ = lean_unbox(v_flag_5539_);
v_res_5541_ = l_Lean_Expr_setPPUniverses(v_e_5538_, v_flag_boxed_5540_);
return v_res_5541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5546_, uint8_t v_flag_5547_){
_start:
{
lean_object* v___x_5548_; lean_object* v___x_5549_; 
v___x_5548_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5549_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5546_, v___x_5548_, v_flag_5547_);
return v___x_5549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5550_, lean_object* v_flag_5551_){
_start:
{
uint8_t v_flag_boxed_5552_; lean_object* v_res_5553_; 
v_flag_boxed_5552_ = lean_unbox(v_flag_5551_);
v_res_5553_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5550_, v_flag_boxed_5552_);
return v_res_5553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5558_, uint8_t v_flag_5559_){
_start:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; 
v___x_5560_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5561_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5558_, v___x_5560_, v_flag_5559_);
return v___x_5561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5562_, lean_object* v_flag_5563_){
_start:
{
uint8_t v_flag_boxed_5564_; lean_object* v_res_5565_; 
v_flag_boxed_5564_ = lean_unbox(v_flag_5563_);
v_res_5565_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5562_, v_flag_boxed_5564_);
return v_res_5565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5570_, uint8_t v_flag_5571_){
_start:
{
lean_object* v___x_5572_; lean_object* v___x_5573_; 
v___x_5572_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5573_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5570_, v___x_5572_, v_flag_5571_);
return v___x_5573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5574_, lean_object* v_flag_5575_){
_start:
{
uint8_t v_flag_boxed_5576_; lean_object* v_res_5577_; 
v_flag_boxed_5576_ = lean_unbox(v_flag_5575_);
v_res_5577_ = l_Lean_Expr_setPPNumericTypes(v_e_5574_, v_flag_boxed_5576_);
return v_res_5577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5578_, size_t v_i_5579_, lean_object* v_bs_5580_){
_start:
{
uint8_t v___x_5581_; 
v___x_5581_ = lean_usize_dec_lt(v_i_5579_, v_sz_5578_);
if (v___x_5581_ == 0)
{
return v_bs_5580_;
}
else
{
uint8_t v___x_5582_; lean_object* v_v_5583_; lean_object* v___x_5584_; lean_object* v_bs_x27_5585_; lean_object* v___x_5586_; size_t v___x_5587_; size_t v___x_5588_; lean_object* v___x_5589_; 
v___x_5582_ = 0;
v_v_5583_ = lean_array_uget(v_bs_5580_, v_i_5579_);
v___x_5584_ = lean_unsigned_to_nat(0u);
v_bs_x27_5585_ = lean_array_uset(v_bs_5580_, v_i_5579_, v___x_5584_);
v___x_5586_ = l_Lean_Expr_setPPExplicit(v_v_5583_, v___x_5582_);
v___x_5587_ = ((size_t)1ULL);
v___x_5588_ = lean_usize_add(v_i_5579_, v___x_5587_);
v___x_5589_ = lean_array_uset(v_bs_x27_5585_, v_i_5579_, v___x_5586_);
v_i_5579_ = v___x_5588_;
v_bs_5580_ = v___x_5589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5591_, lean_object* v_i_5592_, lean_object* v_bs_5593_){
_start:
{
size_t v_sz_boxed_5594_; size_t v_i_boxed_5595_; lean_object* v_res_5596_; 
v_sz_boxed_5594_ = lean_unbox_usize(v_sz_5591_);
lean_dec(v_sz_5591_);
v_i_boxed_5595_ = lean_unbox_usize(v_i_5592_);
lean_dec(v_i_5592_);
v_res_5596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5594_, v_i_boxed_5595_, v_bs_5593_);
return v_res_5596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5597_){
_start:
{
if (lean_obj_tag(v_e_5597_) == 5)
{
lean_object* v___x_5598_; uint8_t v___x_5599_; lean_object* v_f_5600_; lean_object* v_dummy_5601_; lean_object* v_nargs_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; size_t v_sz_5607_; size_t v___x_5608_; lean_object* v_args_5609_; lean_object* v___x_5610_; uint8_t v___x_5611_; lean_object* v___x_5612_; 
v___x_5598_ = l_Lean_Expr_getAppFn(v_e_5597_);
v___x_5599_ = 0;
v_f_5600_ = l_Lean_Expr_setPPExplicit(v___x_5598_, v___x_5599_);
v_dummy_5601_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5602_ = l_Lean_Expr_getAppNumArgs(v_e_5597_);
lean_inc(v_nargs_5602_);
v___x_5603_ = lean_mk_array(v_nargs_5602_, v_dummy_5601_);
v___x_5604_ = lean_unsigned_to_nat(1u);
v___x_5605_ = lean_nat_sub(v_nargs_5602_, v___x_5604_);
lean_dec(v_nargs_5602_);
v___x_5606_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5597_, v___x_5603_, v___x_5605_);
v_sz_5607_ = lean_array_size(v___x_5606_);
v___x_5608_ = ((size_t)0ULL);
v_args_5609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5607_, v___x_5608_, v___x_5606_);
v___x_5610_ = l_Lean_mkAppN(v_f_5600_, v_args_5609_);
lean_dec_ref(v_args_5609_);
v___x_5611_ = 1;
v___x_5612_ = l_Lean_Expr_setPPExplicit(v___x_5610_, v___x_5611_);
return v___x_5612_;
}
else
{
return v_e_5597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5613_, size_t v_i_5614_, lean_object* v_bs_5615_){
_start:
{
uint8_t v___x_5616_; 
v___x_5616_ = lean_usize_dec_lt(v_i_5614_, v_sz_5613_);
if (v___x_5616_ == 0)
{
return v_bs_5615_;
}
else
{
lean_object* v_v_5617_; lean_object* v___x_5618_; lean_object* v_bs_x27_5619_; lean_object* v___y_5621_; uint8_t v___x_5626_; 
v_v_5617_ = lean_array_uget(v_bs_5615_, v_i_5614_);
v___x_5618_ = lean_unsigned_to_nat(0u);
v_bs_x27_5619_ = lean_array_uset(v_bs_5615_, v_i_5614_, v___x_5618_);
v___x_5626_ = l_Lean_Expr_hasMVar(v_v_5617_);
if (v___x_5626_ == 0)
{
lean_object* v___x_5627_; 
v___x_5627_ = l_Lean_Expr_setPPExplicit(v_v_5617_, v___x_5626_);
v___y_5621_ = v___x_5627_;
goto v___jp_5620_;
}
else
{
v___y_5621_ = v_v_5617_;
goto v___jp_5620_;
}
v___jp_5620_:
{
size_t v___x_5622_; size_t v___x_5623_; lean_object* v___x_5624_; 
v___x_5622_ = ((size_t)1ULL);
v___x_5623_ = lean_usize_add(v_i_5614_, v___x_5622_);
v___x_5624_ = lean_array_uset(v_bs_x27_5619_, v_i_5614_, v___y_5621_);
v_i_5614_ = v___x_5623_;
v_bs_5615_ = v___x_5624_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5628_, lean_object* v_i_5629_, lean_object* v_bs_5630_){
_start:
{
size_t v_sz_boxed_5631_; size_t v_i_boxed_5632_; lean_object* v_res_5633_; 
v_sz_boxed_5631_ = lean_unbox_usize(v_sz_5628_);
lean_dec(v_sz_5628_);
v_i_boxed_5632_ = lean_unbox_usize(v_i_5629_);
lean_dec(v_i_5629_);
v_res_5633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5631_, v_i_boxed_5632_, v_bs_5630_);
return v_res_5633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5634_){
_start:
{
if (lean_obj_tag(v_e_5634_) == 5)
{
lean_object* v___x_5635_; uint8_t v___x_5636_; lean_object* v_f_5637_; lean_object* v_dummy_5638_; lean_object* v_nargs_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; size_t v_sz_5644_; size_t v___x_5645_; lean_object* v_args_5646_; lean_object* v___x_5647_; uint8_t v___x_5648_; lean_object* v___x_5649_; 
v___x_5635_ = l_Lean_Expr_getAppFn(v_e_5634_);
v___x_5636_ = 0;
v_f_5637_ = l_Lean_Expr_setPPExplicit(v___x_5635_, v___x_5636_);
v_dummy_5638_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5639_ = l_Lean_Expr_getAppNumArgs(v_e_5634_);
lean_inc(v_nargs_5639_);
v___x_5640_ = lean_mk_array(v_nargs_5639_, v_dummy_5638_);
v___x_5641_ = lean_unsigned_to_nat(1u);
v___x_5642_ = lean_nat_sub(v_nargs_5639_, v___x_5641_);
lean_dec(v_nargs_5639_);
v___x_5643_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5634_, v___x_5640_, v___x_5642_);
v_sz_5644_ = lean_array_size(v___x_5643_);
v___x_5645_ = ((size_t)0ULL);
v_args_5646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5644_, v___x_5645_, v___x_5643_);
v___x_5647_ = l_Lean_mkAppN(v_f_5637_, v_args_5646_);
lean_dec_ref(v_args_5646_);
v___x_5648_ = 1;
v___x_5649_ = l_Lean_Expr_setPPExplicit(v___x_5647_, v___x_5648_);
return v___x_5649_;
}
else
{
return v_e_5634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5650_, lean_object* v_body_5651_, lean_object* v_x_5652_){
_start:
{
lean_object* v___x_5653_; 
v___x_5653_ = lean_apply_1(v_f_5650_, v_body_5651_);
return v___x_5653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5654_, lean_object* v_binderType_5655_, lean_object* v_x_5656_){
_start:
{
lean_object* v___x_5657_; 
v___x_5657_ = lean_apply_1(v_f_5654_, v_binderType_5655_);
return v___x_5657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5658_, lean_object* v_value_5659_, lean_object* v_x_5660_){
_start:
{
lean_object* v___x_5661_; 
v___x_5661_ = lean_apply_1(v_f_5658_, v_value_5659_);
return v___x_5661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5662_, lean_object* v_type_5663_, lean_object* v_x_5664_){
_start:
{
lean_object* v___x_5665_; 
v___x_5665_ = lean_apply_1(v_f_5662_, v_type_5663_);
return v___x_5665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5666_, lean_object* v_arg_5667_, lean_object* v_x_5668_){
_start:
{
lean_object* v___x_5669_; 
v___x_5669_ = lean_apply_1(v_f_5666_, v_arg_5667_);
return v___x_5669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5670_, lean_object* v_fn_5671_, lean_object* v_x_5672_){
_start:
{
lean_object* v___x_5673_; 
v___x_5673_ = lean_apply_1(v_f_5670_, v_fn_5671_);
return v___x_5673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5674_, lean_object* v_f_5675_, lean_object* v_x_5676_){
_start:
{
switch(lean_obj_tag(v_x_5676_))
{
case 7:
{
lean_object* v_toPure_5677_; lean_object* v_toSeq_5678_; lean_object* v_binderType_5679_; lean_object* v_body_5680_; lean_object* v___f_5681_; lean_object* v___f_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; 
v_toPure_5677_ = lean_ctor_get(v_inst_5674_, 1);
lean_inc(v_toPure_5677_);
v_toSeq_5678_ = lean_ctor_get(v_inst_5674_, 2);
lean_inc_n(v_toSeq_5678_, 2);
lean_dec_ref(v_inst_5674_);
v_binderType_5679_ = lean_ctor_get(v_x_5676_, 1);
v_body_5680_ = lean_ctor_get(v_x_5676_, 2);
lean_inc_ref(v_body_5680_);
lean_inc(v_f_5675_);
v___f_5681_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5681_, 0, v_f_5675_);
lean_closure_set(v___f_5681_, 1, v_body_5680_);
lean_inc_ref(v_binderType_5679_);
v___f_5682_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5682_, 0, v_f_5675_);
lean_closure_set(v___f_5682_, 1, v_binderType_5679_);
v___x_5683_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5683_, 0, v_x_5676_);
v___x_5684_ = lean_apply_2(v_toPure_5677_, lean_box(0), v___x_5683_);
v___x_5685_ = lean_apply_4(v_toSeq_5678_, lean_box(0), lean_box(0), v___x_5684_, v___f_5682_);
v___x_5686_ = lean_apply_4(v_toSeq_5678_, lean_box(0), lean_box(0), v___x_5685_, v___f_5681_);
return v___x_5686_;
}
case 6:
{
lean_object* v_toPure_5687_; lean_object* v_toSeq_5688_; lean_object* v_binderType_5689_; lean_object* v_body_5690_; lean_object* v___f_5691_; lean_object* v___f_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; 
v_toPure_5687_ = lean_ctor_get(v_inst_5674_, 1);
lean_inc(v_toPure_5687_);
v_toSeq_5688_ = lean_ctor_get(v_inst_5674_, 2);
lean_inc_n(v_toSeq_5688_, 2);
lean_dec_ref(v_inst_5674_);
v_binderType_5689_ = lean_ctor_get(v_x_5676_, 1);
v_body_5690_ = lean_ctor_get(v_x_5676_, 2);
lean_inc_ref(v_body_5690_);
lean_inc(v_f_5675_);
v___f_5691_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5691_, 0, v_f_5675_);
lean_closure_set(v___f_5691_, 1, v_body_5690_);
lean_inc_ref(v_binderType_5689_);
v___f_5692_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5692_, 0, v_f_5675_);
lean_closure_set(v___f_5692_, 1, v_binderType_5689_);
v___x_5693_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5693_, 0, v_x_5676_);
v___x_5694_ = lean_apply_2(v_toPure_5687_, lean_box(0), v___x_5693_);
v___x_5695_ = lean_apply_4(v_toSeq_5688_, lean_box(0), lean_box(0), v___x_5694_, v___f_5692_);
v___x_5696_ = lean_apply_4(v_toSeq_5688_, lean_box(0), lean_box(0), v___x_5695_, v___f_5691_);
return v___x_5696_;
}
case 10:
{
lean_object* v_toFunctor_5697_; lean_object* v_expr_5698_; lean_object* v_map_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; 
v_toFunctor_5697_ = lean_ctor_get(v_inst_5674_, 0);
lean_inc_ref(v_toFunctor_5697_);
lean_dec_ref(v_inst_5674_);
v_expr_5698_ = lean_ctor_get(v_x_5676_, 1);
lean_inc_ref(v_expr_5698_);
v_map_5699_ = lean_ctor_get(v_toFunctor_5697_, 0);
lean_inc(v_map_5699_);
lean_dec_ref(v_toFunctor_5697_);
v___x_5700_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5700_, 0, v_x_5676_);
v___x_5701_ = lean_apply_1(v_f_5675_, v_expr_5698_);
v___x_5702_ = lean_apply_4(v_map_5699_, lean_box(0), lean_box(0), v___x_5700_, v___x_5701_);
return v___x_5702_;
}
case 8:
{
lean_object* v_toPure_5703_; lean_object* v_toSeq_5704_; lean_object* v_type_5705_; lean_object* v_value_5706_; lean_object* v_body_5707_; lean_object* v___f_5708_; lean_object* v___f_5709_; lean_object* v___f_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; 
v_toPure_5703_ = lean_ctor_get(v_inst_5674_, 1);
lean_inc(v_toPure_5703_);
v_toSeq_5704_ = lean_ctor_get(v_inst_5674_, 2);
lean_inc_n(v_toSeq_5704_, 3);
lean_dec_ref(v_inst_5674_);
v_type_5705_ = lean_ctor_get(v_x_5676_, 1);
v_value_5706_ = lean_ctor_get(v_x_5676_, 2);
v_body_5707_ = lean_ctor_get(v_x_5676_, 3);
lean_inc_ref(v_body_5707_);
lean_inc_n(v_f_5675_, 2);
v___f_5708_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5708_, 0, v_f_5675_);
lean_closure_set(v___f_5708_, 1, v_body_5707_);
lean_inc_ref(v_value_5706_);
v___f_5709_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5709_, 0, v_f_5675_);
lean_closure_set(v___f_5709_, 1, v_value_5706_);
lean_inc_ref(v_type_5705_);
v___f_5710_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5710_, 0, v_f_5675_);
lean_closure_set(v___f_5710_, 1, v_type_5705_);
v___x_5711_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5711_, 0, v_x_5676_);
v___x_5712_ = lean_apply_2(v_toPure_5703_, lean_box(0), v___x_5711_);
v___x_5713_ = lean_apply_4(v_toSeq_5704_, lean_box(0), lean_box(0), v___x_5712_, v___f_5710_);
v___x_5714_ = lean_apply_4(v_toSeq_5704_, lean_box(0), lean_box(0), v___x_5713_, v___f_5709_);
v___x_5715_ = lean_apply_4(v_toSeq_5704_, lean_box(0), lean_box(0), v___x_5714_, v___f_5708_);
return v___x_5715_;
}
case 5:
{
lean_object* v_toPure_5716_; lean_object* v_toSeq_5717_; lean_object* v_fn_5718_; lean_object* v_arg_5719_; lean_object* v___f_5720_; lean_object* v___f_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; 
v_toPure_5716_ = lean_ctor_get(v_inst_5674_, 1);
lean_inc(v_toPure_5716_);
v_toSeq_5717_ = lean_ctor_get(v_inst_5674_, 2);
lean_inc_n(v_toSeq_5717_, 2);
lean_dec_ref(v_inst_5674_);
v_fn_5718_ = lean_ctor_get(v_x_5676_, 0);
v_arg_5719_ = lean_ctor_get(v_x_5676_, 1);
lean_inc_ref(v_arg_5719_);
lean_inc(v_f_5675_);
v___f_5720_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5720_, 0, v_f_5675_);
lean_closure_set(v___f_5720_, 1, v_arg_5719_);
lean_inc_ref(v_fn_5718_);
v___f_5721_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5721_, 0, v_f_5675_);
lean_closure_set(v___f_5721_, 1, v_fn_5718_);
v___x_5722_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5722_, 0, v_x_5676_);
v___x_5723_ = lean_apply_2(v_toPure_5716_, lean_box(0), v___x_5722_);
v___x_5724_ = lean_apply_4(v_toSeq_5717_, lean_box(0), lean_box(0), v___x_5723_, v___f_5721_);
v___x_5725_ = lean_apply_4(v_toSeq_5717_, lean_box(0), lean_box(0), v___x_5724_, v___f_5720_);
return v___x_5725_;
}
case 11:
{
lean_object* v_toFunctor_5726_; lean_object* v_struct_5727_; lean_object* v_map_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; 
v_toFunctor_5726_ = lean_ctor_get(v_inst_5674_, 0);
lean_inc_ref(v_toFunctor_5726_);
lean_dec_ref(v_inst_5674_);
v_struct_5727_ = lean_ctor_get(v_x_5676_, 2);
lean_inc_ref(v_struct_5727_);
v_map_5728_ = lean_ctor_get(v_toFunctor_5726_, 0);
lean_inc(v_map_5728_);
lean_dec_ref(v_toFunctor_5726_);
v___x_5729_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5729_, 0, v_x_5676_);
v___x_5730_ = lean_apply_1(v_f_5675_, v_struct_5727_);
v___x_5731_ = lean_apply_4(v_map_5728_, lean_box(0), lean_box(0), v___x_5729_, v___x_5730_);
return v___x_5731_;
}
default: 
{
lean_object* v_toPure_5732_; lean_object* v___x_5733_; 
lean_dec(v_f_5675_);
v_toPure_5732_ = lean_ctor_get(v_inst_5674_, 1);
lean_inc(v_toPure_5732_);
lean_dec_ref(v_inst_5674_);
v___x_5733_ = lean_apply_2(v_toPure_5732_, lean_box(0), v_x_5676_);
return v___x_5733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5734_, lean_object* v_inst_5735_, lean_object* v_f_5736_, lean_object* v_x_5737_){
_start:
{
lean_object* v___x_5738_; 
v___x_5738_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5735_, v_f_5736_, v_x_5737_);
return v___x_5738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5739_){
_start:
{
lean_object* v_snd_5740_; 
v_snd_5740_ = lean_ctor_get(v_self_5739_, 1);
lean_inc(v_snd_5740_);
return v_snd_5740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5741_){
_start:
{
lean_object* v_res_5742_; 
v_res_5742_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5741_);
lean_dec_ref(v_self_5741_);
return v_res_5742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5743_, lean_object* v_snd_5744_){
_start:
{
lean_object* v___x_5745_; 
v___x_5745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5745_, 0, v_e_x27_5743_);
lean_ctor_set(v___x_5745_, 1, v_snd_5744_);
return v___x_5745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5746_, lean_object* v_map_5747_, lean_object* v_e_x27_5748_, lean_object* v_a_5749_){
_start:
{
lean_object* v___f_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; 
lean_inc_ref(v_e_x27_5748_);
v___f_5750_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5750_, 0, v_e_x27_5748_);
v___x_5751_ = lean_apply_2(v_f_5746_, v_a_5749_, v_e_x27_5748_);
v___x_5752_ = lean_apply_4(v_map_5747_, lean_box(0), lean_box(0), v___f_5750_, v___x_5751_);
return v___x_5752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5754_, lean_object* v_f_5755_, lean_object* v_init_5756_, lean_object* v_e_5757_){
_start:
{
lean_object* v_toApplicative_5758_; lean_object* v_toFunctor_5759_; lean_object* v___x_5761_; uint8_t v_isShared_5762_; uint8_t v_isSharedCheck_5786_; 
v_toApplicative_5758_ = lean_ctor_get(v_inst_5754_, 0);
lean_inc_ref(v_toApplicative_5758_);
v_toFunctor_5759_ = lean_ctor_get(v_toApplicative_5758_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v_toApplicative_5758_);
if (v_isSharedCheck_5786_ == 0)
{
lean_object* v_unused_5787_; lean_object* v_unused_5788_; lean_object* v_unused_5789_; lean_object* v_unused_5790_; 
v_unused_5787_ = lean_ctor_get(v_toApplicative_5758_, 4);
lean_dec(v_unused_5787_);
v_unused_5788_ = lean_ctor_get(v_toApplicative_5758_, 3);
lean_dec(v_unused_5788_);
v_unused_5789_ = lean_ctor_get(v_toApplicative_5758_, 2);
lean_dec(v_unused_5789_);
v_unused_5790_ = lean_ctor_get(v_toApplicative_5758_, 1);
lean_dec(v_unused_5790_);
v___x_5761_ = v_toApplicative_5758_;
v_isShared_5762_ = v_isSharedCheck_5786_;
goto v_resetjp_5760_;
}
else
{
lean_inc(v_toFunctor_5759_);
lean_dec(v_toApplicative_5758_);
v___x_5761_ = lean_box(0);
v_isShared_5762_ = v_isSharedCheck_5786_;
goto v_resetjp_5760_;
}
v_resetjp_5760_:
{
lean_object* v_map_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5784_; 
v_map_5763_ = lean_ctor_get(v_toFunctor_5759_, 0);
v_isSharedCheck_5784_ = !lean_is_exclusive(v_toFunctor_5759_);
if (v_isSharedCheck_5784_ == 0)
{
lean_object* v_unused_5785_; 
v_unused_5785_ = lean_ctor_get(v_toFunctor_5759_, 1);
lean_dec(v_unused_5785_);
v___x_5765_ = v_toFunctor_5759_;
v_isShared_5766_ = v_isSharedCheck_5784_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_map_5763_);
lean_dec(v_toFunctor_5759_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5784_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v___f_5767_; lean_object* v___f_5768_; lean_object* v___f_5769_; lean_object* v___f_5770_; lean_object* v___f_5771_; lean_object* v___f_5772_; lean_object* v___x_5773_; lean_object* v___x_5775_; 
v___f_5767_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5763_);
v___f_5768_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5768_, 0, v_f_5755_);
lean_closure_set(v___f_5768_, 1, v_map_5763_);
lean_inc_ref_n(v_inst_5754_, 5);
v___f_5769_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5769_, 0, v_inst_5754_);
v___f_5770_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5770_, 0, v_inst_5754_);
v___f_5771_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5771_, 0, v_inst_5754_);
v___f_5772_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5772_, 0, v_inst_5754_);
v___x_5773_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5773_, 0, lean_box(0));
lean_closure_set(v___x_5773_, 1, lean_box(0));
lean_closure_set(v___x_5773_, 2, v_inst_5754_);
if (v_isShared_5766_ == 0)
{
lean_ctor_set(v___x_5765_, 1, v___f_5769_);
lean_ctor_set(v___x_5765_, 0, v___x_5773_);
v___x_5775_ = v___x_5765_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v___x_5773_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v___f_5769_);
v___x_5775_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
lean_object* v___x_5776_; lean_object* v___x_5778_; 
v___x_5776_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5776_, 0, lean_box(0));
lean_closure_set(v___x_5776_, 1, lean_box(0));
lean_closure_set(v___x_5776_, 2, v_inst_5754_);
if (v_isShared_5762_ == 0)
{
lean_ctor_set(v___x_5761_, 4, v___f_5772_);
lean_ctor_set(v___x_5761_, 3, v___f_5771_);
lean_ctor_set(v___x_5761_, 2, v___f_5770_);
lean_ctor_set(v___x_5761_, 1, v___x_5776_);
lean_ctor_set(v___x_5761_, 0, v___x_5775_);
v___x_5778_ = v___x_5761_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v___x_5775_);
lean_ctor_set(v_reuseFailAlloc_5782_, 1, v___x_5776_);
lean_ctor_set(v_reuseFailAlloc_5782_, 2, v___f_5770_);
lean_ctor_set(v_reuseFailAlloc_5782_, 3, v___f_5771_);
lean_ctor_set(v_reuseFailAlloc_5782_, 4, v___f_5772_);
v___x_5778_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
lean_object* v___x_30__overap_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; 
v___x_30__overap_5779_ = l_Lean_Expr_traverseChildren___redArg(v___x_5778_, v___f_5768_, v_e_5757_);
v___x_5780_ = lean_apply_1(v___x_30__overap_5779_, v_init_5756_);
v___x_5781_ = lean_apply_4(v_map_5763_, lean_box(0), lean_box(0), v___f_5767_, v___x_5780_);
return v___x_5781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5791_, lean_object* v_m_5792_, lean_object* v_inst_5793_, lean_object* v_f_5794_, lean_object* v_init_5795_, lean_object* v_e_5796_){
_start:
{
lean_object* v___x_5797_; 
v___x_5797_ = l_Lean_Expr_foldlM___redArg(v_inst_5793_, v_f_5794_, v_init_5795_, v_e_5796_);
return v___x_5797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5798_){
_start:
{
lean_object* v_d_5800_; lean_object* v_b_5801_; 
switch(lean_obj_tag(v_x_5798_))
{
case 5:
{
lean_object* v_fn_5807_; lean_object* v_arg_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; 
v_fn_5807_ = lean_ctor_get(v_x_5798_, 0);
v_arg_5808_ = lean_ctor_get(v_x_5798_, 1);
v___x_5809_ = lean_unsigned_to_nat(1u);
v___x_5810_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5807_);
v___x_5811_ = lean_nat_add(v___x_5809_, v___x_5810_);
lean_dec(v___x_5810_);
v___x_5812_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5808_);
v___x_5813_ = lean_nat_add(v___x_5811_, v___x_5812_);
lean_dec(v___x_5812_);
lean_dec(v___x_5811_);
return v___x_5813_;
}
case 6:
{
lean_object* v_binderType_5814_; lean_object* v_body_5815_; 
v_binderType_5814_ = lean_ctor_get(v_x_5798_, 1);
v_body_5815_ = lean_ctor_get(v_x_5798_, 2);
v_d_5800_ = v_binderType_5814_;
v_b_5801_ = v_body_5815_;
goto v___jp_5799_;
}
case 7:
{
lean_object* v_binderType_5816_; lean_object* v_body_5817_; 
v_binderType_5816_ = lean_ctor_get(v_x_5798_, 1);
v_body_5817_ = lean_ctor_get(v_x_5798_, 2);
v_d_5800_ = v_binderType_5816_;
v_b_5801_ = v_body_5817_;
goto v___jp_5799_;
}
case 8:
{
lean_object* v_type_5818_; lean_object* v_value_5819_; lean_object* v_body_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; 
v_type_5818_ = lean_ctor_get(v_x_5798_, 1);
v_value_5819_ = lean_ctor_get(v_x_5798_, 2);
v_body_5820_ = lean_ctor_get(v_x_5798_, 3);
v___x_5821_ = lean_unsigned_to_nat(1u);
v___x_5822_ = l_Lean_Expr_sizeWithoutSharing(v_type_5818_);
v___x_5823_ = lean_nat_add(v___x_5821_, v___x_5822_);
lean_dec(v___x_5822_);
v___x_5824_ = l_Lean_Expr_sizeWithoutSharing(v_value_5819_);
v___x_5825_ = lean_nat_add(v___x_5823_, v___x_5824_);
lean_dec(v___x_5824_);
lean_dec(v___x_5823_);
v___x_5826_ = l_Lean_Expr_sizeWithoutSharing(v_body_5820_);
v___x_5827_ = lean_nat_add(v___x_5825_, v___x_5826_);
lean_dec(v___x_5826_);
lean_dec(v___x_5825_);
return v___x_5827_;
}
case 10:
{
lean_object* v_expr_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; 
v_expr_5828_ = lean_ctor_get(v_x_5798_, 1);
v___x_5829_ = lean_unsigned_to_nat(1u);
v___x_5830_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5828_);
v___x_5831_ = lean_nat_add(v___x_5829_, v___x_5830_);
lean_dec(v___x_5830_);
return v___x_5831_;
}
case 11:
{
lean_object* v_struct_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; 
v_struct_5832_ = lean_ctor_get(v_x_5798_, 2);
v___x_5833_ = lean_unsigned_to_nat(1u);
v___x_5834_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5832_);
v___x_5835_ = lean_nat_add(v___x_5833_, v___x_5834_);
lean_dec(v___x_5834_);
return v___x_5835_;
}
default: 
{
lean_object* v___x_5836_; 
v___x_5836_ = lean_unsigned_to_nat(1u);
return v___x_5836_;
}
}
v___jp_5799_:
{
lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; 
v___x_5802_ = lean_unsigned_to_nat(1u);
v___x_5803_ = l_Lean_Expr_sizeWithoutSharing(v_d_5800_);
v___x_5804_ = lean_nat_add(v___x_5802_, v___x_5803_);
lean_dec(v___x_5803_);
v___x_5805_ = l_Lean_Expr_sizeWithoutSharing(v_b_5801_);
v___x_5806_ = lean_nat_add(v___x_5804_, v___x_5805_);
lean_dec(v___x_5805_);
lean_dec(v___x_5804_);
return v___x_5806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5837_){
_start:
{
lean_object* v_res_5838_; 
v_res_5838_ = l_Lean_Expr_sizeWithoutSharing(v_x_5837_);
lean_dec_ref(v_x_5837_);
return v_res_5838_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5841_, lean_object* v_e_5842_){
_start:
{
lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; 
v___x_5843_ = l_Lean_KVMap_empty;
v___x_5844_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5845_ = l_Lean_KVMap_insert(v___x_5843_, v_kind_5841_, v___x_5844_);
v___x_5846_ = l_Lean_Expr_mdata___override(v___x_5845_, v_e_5842_);
return v___x_5846_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5847_, lean_object* v_e_5848_){
_start:
{
if (lean_obj_tag(v_e_5848_) == 10)
{
lean_object* v_data_5849_; lean_object* v_expr_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; uint8_t v___x_5853_; 
v_data_5849_ = lean_ctor_get(v_e_5848_, 0);
v_expr_5850_ = lean_ctor_get(v_e_5848_, 1);
v___x_5851_ = l_Lean_KVMap_size(v_data_5849_);
v___x_5852_ = lean_unsigned_to_nat(1u);
v___x_5853_ = lean_nat_dec_eq(v___x_5851_, v___x_5852_);
lean_dec(v___x_5851_);
if (v___x_5853_ == 0)
{
lean_object* v___x_5854_; 
v___x_5854_ = lean_box(0);
return v___x_5854_;
}
else
{
uint8_t v___x_5855_; uint8_t v___x_5856_; 
v___x_5855_ = 0;
v___x_5856_ = l_Lean_KVMap_getBool(v_data_5849_, v_kind_5847_, v___x_5855_);
if (v___x_5856_ == 0)
{
lean_object* v___x_5857_; 
v___x_5857_ = lean_box(0);
return v___x_5857_;
}
else
{
lean_object* v___x_5858_; 
lean_inc_ref(v_expr_5850_);
v___x_5858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5858_, 0, v_expr_5850_);
return v___x_5858_;
}
}
}
else
{
lean_object* v___x_5859_; 
v___x_5859_ = lean_box(0);
return v___x_5859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5860_, lean_object* v_e_5861_){
_start:
{
lean_object* v_res_5862_; 
v_res_5862_ = l_Lean_annotation_x3f(v_kind_5860_, v_e_5861_);
lean_dec_ref(v_e_5861_);
lean_dec(v_kind_5860_);
return v_res_5862_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5866_){
_start:
{
lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5867_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5868_ = l_Lean_mkAnnotation(v___x_5867_, v_e_5866_);
return v___x_5868_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5869_){
_start:
{
lean_object* v___x_5870_; lean_object* v___x_5871_; 
v___x_5870_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5871_ = l_Lean_annotation_x3f(v___x_5870_, v_e_5869_);
return v___x_5871_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5872_){
_start:
{
lean_object* v_res_5873_; 
v_res_5873_ = l_Lean_inaccessible_x3f(v_e_5872_);
lean_dec_ref(v_e_5872_);
return v_res_5873_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5878_){
_start:
{
if (lean_obj_tag(v_p_5878_) == 10)
{
lean_object* v_data_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; 
v_data_5879_ = lean_ctor_get(v_p_5878_, 0);
v___x_5880_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5881_ = l_Lean_KVMap_find(v_data_5879_, v___x_5880_);
if (lean_obj_tag(v___x_5881_) == 1)
{
lean_object* v_val_5882_; lean_object* v___x_5884_; uint8_t v_isShared_5885_; uint8_t v_isSharedCheck_5893_; 
v_val_5882_ = lean_ctor_get(v___x_5881_, 0);
v_isSharedCheck_5893_ = !lean_is_exclusive(v___x_5881_);
if (v_isSharedCheck_5893_ == 0)
{
v___x_5884_ = v___x_5881_;
v_isShared_5885_ = v_isSharedCheck_5893_;
goto v_resetjp_5883_;
}
else
{
lean_inc(v_val_5882_);
lean_dec(v___x_5881_);
v___x_5884_ = lean_box(0);
v_isShared_5885_ = v_isSharedCheck_5893_;
goto v_resetjp_5883_;
}
v_resetjp_5883_:
{
if (lean_obj_tag(v_val_5882_) == 5)
{
lean_object* v_v_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5890_; 
v_v_5886_ = lean_ctor_get(v_val_5882_, 0);
lean_inc(v_v_5886_);
lean_dec_ref_known(v_val_5882_, 1);
v___x_5887_ = l_Lean_Expr_mdataExpr_x21(v_p_5878_);
v___x_5888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5888_, 0, v_v_5886_);
lean_ctor_set(v___x_5888_, 1, v___x_5887_);
if (v_isShared_5885_ == 0)
{
lean_ctor_set(v___x_5884_, 0, v___x_5888_);
v___x_5890_ = v___x_5884_;
goto v_reusejp_5889_;
}
else
{
lean_object* v_reuseFailAlloc_5891_; 
v_reuseFailAlloc_5891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5891_, 0, v___x_5888_);
v___x_5890_ = v_reuseFailAlloc_5891_;
goto v_reusejp_5889_;
}
v_reusejp_5889_:
{
return v___x_5890_;
}
}
else
{
lean_object* v___x_5892_; 
lean_del_object(v___x_5884_);
lean_dec(v_val_5882_);
v___x_5892_ = lean_box(0);
return v___x_5892_;
}
}
}
else
{
lean_object* v___x_5894_; 
lean_dec(v___x_5881_);
v___x_5894_ = lean_box(0);
return v___x_5894_;
}
}
else
{
lean_object* v___x_5895_; 
v___x_5895_ = lean_box(0);
return v___x_5895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5896_){
_start:
{
lean_object* v_res_5897_; 
v_res_5897_ = l_Lean_patternWithRef_x3f(v_p_5896_);
lean_dec_ref(v_p_5896_);
return v_res_5897_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5898_){
_start:
{
lean_object* v___x_5899_; 
v___x_5899_ = l_Lean_patternWithRef_x3f(v_p_5898_);
if (lean_obj_tag(v___x_5899_) == 0)
{
uint8_t v___x_5900_; 
v___x_5900_ = 0;
return v___x_5900_;
}
else
{
uint8_t v___x_5901_; 
lean_dec_ref_known(v___x_5899_, 1);
v___x_5901_ = 1;
return v___x_5901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5902_){
_start:
{
uint8_t v_res_5903_; lean_object* v_r_5904_; 
v_res_5903_ = l_Lean_isPatternWithRef(v_p_5902_);
lean_dec_ref(v_p_5902_);
v_r_5904_ = lean_box(v_res_5903_);
return v_r_5904_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5905_, lean_object* v_stx_5906_){
_start:
{
lean_object* v___x_5907_; 
v___x_5907_ = l_Lean_patternWithRef_x3f(v_p_5905_);
if (lean_obj_tag(v___x_5907_) == 0)
{
lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; 
v___x_5908_ = l_Lean_KVMap_empty;
v___x_5909_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5910_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5910_, 0, v_stx_5906_);
v___x_5911_ = l_Lean_KVMap_insert(v___x_5908_, v___x_5909_, v___x_5910_);
v___x_5912_ = l_Lean_Expr_mdata___override(v___x_5911_, v_p_5905_);
return v___x_5912_;
}
else
{
lean_dec_ref_known(v___x_5907_, 1);
lean_dec(v_stx_5906_);
return v_p_5905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5913_){
_start:
{
lean_object* v___x_5914_; 
v___x_5914_ = l_Lean_inaccessible_x3f(v_e_5913_);
if (lean_obj_tag(v___x_5914_) == 1)
{
return v___x_5914_;
}
else
{
lean_object* v___x_5915_; 
lean_dec(v___x_5914_);
v___x_5915_ = l_Lean_patternWithRef_x3f(v_e_5913_);
if (lean_obj_tag(v___x_5915_) == 1)
{
lean_object* v_val_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5924_; 
v_val_5916_ = lean_ctor_get(v___x_5915_, 0);
v_isSharedCheck_5924_ = !lean_is_exclusive(v___x_5915_);
if (v_isSharedCheck_5924_ == 0)
{
v___x_5918_ = v___x_5915_;
v_isShared_5919_ = v_isSharedCheck_5924_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_val_5916_);
lean_dec(v___x_5915_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5924_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v_snd_5920_; lean_object* v___x_5922_; 
v_snd_5920_ = lean_ctor_get(v_val_5916_, 1);
lean_inc(v_snd_5920_);
lean_dec(v_val_5916_);
if (v_isShared_5919_ == 0)
{
lean_ctor_set(v___x_5918_, 0, v_snd_5920_);
v___x_5922_ = v___x_5918_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_snd_5920_);
v___x_5922_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
return v___x_5922_;
}
}
}
else
{
lean_object* v___x_5925_; 
lean_dec(v___x_5915_);
v___x_5925_ = lean_box(0);
return v___x_5925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5926_){
_start:
{
lean_object* v_res_5927_; 
v_res_5927_ = l_Lean_patternAnnotation_x3f(v_e_5926_);
lean_dec_ref(v_e_5926_);
return v_res_5927_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5931_){
_start:
{
lean_object* v___x_5932_; lean_object* v___x_5933_; 
v___x_5932_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5933_ = l_Lean_mkAnnotation(v___x_5932_, v_e_5931_);
return v___x_5933_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5937_){
_start:
{
lean_object* v___x_5938_; lean_object* v___x_5939_; 
v___x_5938_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5939_ = l_Lean_annotation_x3f(v___x_5938_, v_e_5937_);
if (lean_obj_tag(v___x_5939_) == 0)
{
return v___x_5939_;
}
else
{
lean_object* v_val_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5953_; 
v_val_5940_ = lean_ctor_get(v___x_5939_, 0);
v_isSharedCheck_5953_ = !lean_is_exclusive(v___x_5939_);
if (v_isSharedCheck_5953_ == 0)
{
v___x_5942_ = v___x_5939_;
v_isShared_5943_ = v_isSharedCheck_5953_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_val_5940_);
lean_dec(v___x_5939_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5953_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v___x_5944_; lean_object* v___x_5945_; uint8_t v___x_5946_; 
v___x_5944_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5945_ = lean_unsigned_to_nat(3u);
v___x_5946_ = l_Lean_Expr_isAppOfArity(v_val_5940_, v___x_5944_, v___x_5945_);
if (v___x_5946_ == 0)
{
lean_object* v___x_5947_; 
lean_del_object(v___x_5942_);
lean_dec(v_val_5940_);
v___x_5947_ = lean_box(0);
return v___x_5947_;
}
else
{
lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5951_; 
v___x_5948_ = l_Lean_Expr_appFn_x21(v_val_5940_);
lean_dec(v_val_5940_);
v___x_5949_ = l_Lean_Expr_appArg_x21(v___x_5948_);
lean_dec_ref(v___x_5948_);
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 0, v___x_5949_);
v___x_5951_ = v___x_5942_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v___x_5949_);
v___x_5951_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
return v___x_5951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5954_){
_start:
{
lean_object* v_res_5955_; 
v_res_5955_ = l_Lean_isLHSGoal_x3f(v_e_5954_);
lean_dec_ref(v_e_5954_);
return v_res_5955_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5956_, lean_object* v_____do__lift_5957_){
_start:
{
lean_object* v___x_5958_; 
v___x_5958_ = lean_apply_2(v_toPure_5956_, lean_box(0), v_____do__lift_5957_);
return v___x_5958_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5959_, lean_object* v_inst_5960_){
_start:
{
lean_object* v_toApplicative_5961_; lean_object* v_toBind_5962_; lean_object* v_toPure_5963_; lean_object* v___x_5964_; lean_object* v___f_5965_; lean_object* v___x_5966_; 
v_toApplicative_5961_ = lean_ctor_get(v_inst_5959_, 0);
v_toBind_5962_ = lean_ctor_get(v_inst_5959_, 1);
lean_inc(v_toBind_5962_);
v_toPure_5963_ = lean_ctor_get(v_toApplicative_5961_, 1);
lean_inc(v_toPure_5963_);
v___x_5964_ = l_Lean_mkFreshId___redArg(v_inst_5959_, v_inst_5960_);
v___f_5965_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5965_, 0, v_toPure_5963_);
v___x_5966_ = lean_apply_4(v_toBind_5962_, lean_box(0), lean_box(0), v___x_5964_, v___f_5965_);
return v___x_5966_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5967_, lean_object* v_inst_5968_, lean_object* v_inst_5969_){
_start:
{
lean_object* v___x_5970_; 
v___x_5970_ = l_Lean_mkFreshFVarId___redArg(v_inst_5968_, v_inst_5969_);
return v___x_5970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5971_, lean_object* v_inst_5972_){
_start:
{
lean_object* v_toApplicative_5973_; lean_object* v_toBind_5974_; lean_object* v_toPure_5975_; lean_object* v___x_5976_; lean_object* v___f_5977_; lean_object* v___x_5978_; 
v_toApplicative_5973_ = lean_ctor_get(v_inst_5971_, 0);
v_toBind_5974_ = lean_ctor_get(v_inst_5971_, 1);
lean_inc(v_toBind_5974_);
v_toPure_5975_ = lean_ctor_get(v_toApplicative_5973_, 1);
lean_inc(v_toPure_5975_);
v___x_5976_ = l_Lean_mkFreshId___redArg(v_inst_5971_, v_inst_5972_);
v___f_5977_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5977_, 0, v_toPure_5975_);
v___x_5978_ = lean_apply_4(v_toBind_5974_, lean_box(0), lean_box(0), v___x_5976_, v___f_5977_);
return v___x_5978_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5979_, lean_object* v_inst_5980_, lean_object* v_inst_5981_){
_start:
{
lean_object* v___x_5982_; 
v___x_5982_ = l_Lean_mkFreshMVarId___redArg(v_inst_5980_, v_inst_5981_);
return v___x_5982_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5983_, lean_object* v_inst_5984_){
_start:
{
lean_object* v_toApplicative_5985_; lean_object* v_toBind_5986_; lean_object* v_toPure_5987_; lean_object* v___x_5988_; lean_object* v___f_5989_; lean_object* v___x_5990_; 
v_toApplicative_5985_ = lean_ctor_get(v_inst_5983_, 0);
v_toBind_5986_ = lean_ctor_get(v_inst_5983_, 1);
lean_inc(v_toBind_5986_);
v_toPure_5987_ = lean_ctor_get(v_toApplicative_5985_, 1);
lean_inc(v_toPure_5987_);
v___x_5988_ = l_Lean_mkFreshId___redArg(v_inst_5983_, v_inst_5984_);
v___f_5989_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5989_, 0, v_toPure_5987_);
v___x_5990_ = lean_apply_4(v_toBind_5986_, lean_box(0), lean_box(0), v___x_5988_, v___f_5989_);
return v___x_5990_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5991_, lean_object* v_inst_5992_, lean_object* v_inst_5993_){
_start:
{
lean_object* v___x_5994_; 
v___x_5994_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5992_, v_inst_5993_);
return v___x_5994_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; 
v___x_5998_ = lean_box(0);
v___x_5999_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_6000_ = l_Lean_Expr_const___override(v___x_5999_, v___x_5998_);
return v___x_6000_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_6001_){
_start:
{
lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_6002_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_6003_ = l_Lean_Expr_app___override(v___x_6002_, v_p_6001_);
return v___x_6003_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; 
v___x_6007_ = lean_box(0);
v___x_6008_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_6009_ = l_Lean_Expr_const___override(v___x_6008_, v___x_6007_);
return v___x_6009_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_6010_, lean_object* v_q_6011_){
_start:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; 
v___x_6012_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_6013_ = l_Lean_mkAppB(v___x_6012_, v_p_6010_, v_q_6011_);
return v___x_6013_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; 
v___x_6017_ = lean_box(0);
v___x_6018_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_6019_ = l_Lean_Expr_const___override(v___x_6018_, v___x_6017_);
return v___x_6019_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_6020_, lean_object* v_q_6021_){
_start:
{
lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6022_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_6023_ = l_Lean_mkAppB(v___x_6022_, v_p_6020_, v_q_6021_);
return v___x_6023_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; 
v___x_6024_ = lean_box(0);
v___x_6025_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_6026_ = l_Lean_Expr_const___override(v___x_6025_, v___x_6024_);
return v___x_6026_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_6027_){
_start:
{
if (lean_obj_tag(v_x_6027_) == 0)
{
lean_object* v___x_6028_; 
v___x_6028_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_6028_;
}
else
{
lean_object* v_tail_6029_; 
v_tail_6029_ = lean_ctor_get(v_x_6027_, 1);
if (lean_obj_tag(v_tail_6029_) == 0)
{
lean_object* v_head_6030_; 
v_head_6030_ = lean_ctor_get(v_x_6027_, 0);
lean_inc(v_head_6030_);
lean_dec_ref_known(v_x_6027_, 2);
return v_head_6030_;
}
else
{
lean_object* v_head_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; 
lean_inc(v_tail_6029_);
v_head_6031_ = lean_ctor_get(v_x_6027_, 0);
lean_inc(v_head_6031_);
lean_dec_ref_known(v_x_6027_, 2);
v___x_6032_ = l_Lean_mkAndN(v_tail_6029_);
v___x_6033_ = l_Lean_mkAnd(v_head_6031_, v___x_6032_);
return v___x_6033_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; 
v___x_6039_ = lean_box(0);
v___x_6040_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_6041_ = l_Lean_Expr_const___override(v___x_6040_, v___x_6039_);
return v___x_6041_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_6042_){
_start:
{
lean_object* v___x_6043_; lean_object* v___x_6044_; 
v___x_6043_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_6044_ = l_Lean_Expr_app___override(v___x_6043_, v_p_6042_);
return v___x_6044_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; 
v___x_6048_ = lean_box(0);
v___x_6049_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_6050_ = l_Lean_Expr_const___override(v___x_6049_, v___x_6048_);
return v___x_6050_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_6051_, lean_object* v_q_6052_){
_start:
{
lean_object* v___x_6053_; lean_object* v___x_6054_; 
v___x_6053_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_6054_ = l_Lean_mkAppB(v___x_6053_, v_p_6051_, v_q_6052_);
return v___x_6054_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_6055_; 
v___x_6055_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_6055_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; 
v___x_6059_ = lean_box(0);
v___x_6060_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_6061_ = l_Lean_Expr_const___override(v___x_6060_, v___x_6059_);
return v___x_6061_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_6062_; 
v___x_6062_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_6062_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; 
v___x_6066_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6067_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_6068_ = l_Lean_Expr_const___override(v___x_6067_, v___x_6066_);
return v___x_6068_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6069_ = l_Lean_Nat_mkInstAdd;
v___x_6070_ = l_Lean_Nat_mkType;
v___x_6071_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6072_ = l_Lean_mkAppB(v___x_6071_, v___x_6070_, v___x_6069_);
return v___x_6072_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_6073_; 
v___x_6073_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_6073_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
v___x_6077_ = lean_box(0);
v___x_6078_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_6079_ = l_Lean_Expr_const___override(v___x_6078_, v___x_6077_);
return v___x_6079_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_6080_; 
v___x_6080_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_6080_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; 
v___x_6084_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6085_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_6086_ = l_Lean_Expr_const___override(v___x_6085_, v___x_6084_);
return v___x_6086_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; 
v___x_6087_ = l_Lean_Nat_mkInstSub;
v___x_6088_ = l_Lean_Nat_mkType;
v___x_6089_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6090_ = l_Lean_mkAppB(v___x_6089_, v___x_6088_, v___x_6087_);
return v___x_6090_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_6091_; 
v___x_6091_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_6091_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; 
v___x_6095_ = lean_box(0);
v___x_6096_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_6097_ = l_Lean_Expr_const___override(v___x_6096_, v___x_6095_);
return v___x_6097_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_6098_; 
v___x_6098_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_6098_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; 
v___x_6102_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6103_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_6104_ = l_Lean_Expr_const___override(v___x_6103_, v___x_6102_);
return v___x_6104_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; 
v___x_6105_ = l_Lean_Nat_mkInstMul;
v___x_6106_ = l_Lean_Nat_mkType;
v___x_6107_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6108_ = l_Lean_mkAppB(v___x_6107_, v___x_6106_, v___x_6105_);
return v___x_6108_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_6109_; 
v___x_6109_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_6109_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; 
v___x_6114_ = lean_box(0);
v___x_6115_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_6116_ = l_Lean_Expr_const___override(v___x_6115_, v___x_6114_);
return v___x_6116_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_6117_; 
v___x_6117_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_6117_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; 
v___x_6121_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6122_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_6123_ = l_Lean_Expr_const___override(v___x_6122_, v___x_6121_);
return v___x_6123_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; 
v___x_6124_ = l_Lean_Nat_mkInstDiv;
v___x_6125_ = l_Lean_Nat_mkType;
v___x_6126_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6127_ = l_Lean_mkAppB(v___x_6126_, v___x_6125_, v___x_6124_);
return v___x_6127_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_6128_; 
v___x_6128_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_6128_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6133_ = lean_box(0);
v___x_6134_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_6135_ = l_Lean_Expr_const___override(v___x_6134_, v___x_6133_);
return v___x_6135_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_6136_; 
v___x_6136_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_6136_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; 
v___x_6140_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6141_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_6142_ = l_Lean_Expr_const___override(v___x_6141_, v___x_6140_);
return v___x_6142_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; 
v___x_6143_ = l_Lean_Nat_mkInstMod;
v___x_6144_ = l_Lean_Nat_mkType;
v___x_6145_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6146_ = l_Lean_mkAppB(v___x_6145_, v___x_6144_, v___x_6143_);
return v___x_6146_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_6147_; 
v___x_6147_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_6147_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; 
v___x_6151_ = lean_box(0);
v___x_6152_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_6153_ = l_Lean_Expr_const___override(v___x_6152_, v___x_6151_);
return v___x_6153_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_6154_; 
v___x_6154_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_6154_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; 
v___x_6158_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6159_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_6160_ = l_Lean_Expr_const___override(v___x_6159_, v___x_6158_);
return v___x_6160_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; 
v___x_6161_ = l_Lean_Nat_mkInstNatPow;
v___x_6162_ = l_Lean_Nat_mkType;
v___x_6163_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6164_ = l_Lean_mkAppB(v___x_6163_, v___x_6162_, v___x_6161_);
return v___x_6164_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_6165_; 
v___x_6165_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_6165_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; 
v___x_6172_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_6173_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_6174_ = l_Lean_Expr_const___override(v___x_6173_, v___x_6172_);
return v___x_6174_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; 
v___x_6175_ = l_Lean_Nat_mkInstPow;
v___x_6176_ = l_Lean_Nat_mkType;
v___x_6177_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6178_ = l_Lean_mkApp3(v___x_6177_, v___x_6176_, v___x_6176_, v___x_6175_);
return v___x_6178_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_6179_; 
v___x_6179_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_6179_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; 
v___x_6183_ = lean_box(0);
v___x_6184_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_6185_ = l_Lean_Expr_const___override(v___x_6184_, v___x_6183_);
return v___x_6185_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_6186_; 
v___x_6186_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_6186_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; 
v___x_6190_ = lean_box(0);
v___x_6191_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6192_ = l_Lean_Expr_const___override(v___x_6191_, v___x_6190_);
return v___x_6192_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6193_; 
v___x_6193_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6193_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6199_; lean_object* v___x_6200_; 
v___x_6199_ = lean_unsigned_to_nat(0u);
v___x_6200_ = l_Lean_Level_ofNat(v___x_6199_);
return v___x_6200_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; 
v___x_6201_ = lean_box(0);
v___x_6202_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6202_);
lean_ctor_set(v___x_6203_, 1, v___x_6201_);
return v___x_6203_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; 
v___x_6204_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6205_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6206_, 0, v___x_6205_);
lean_ctor_set(v___x_6206_, 1, v___x_6204_);
return v___x_6206_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; 
v___x_6207_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6208_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6209_, 0, v___x_6208_);
lean_ctor_set(v___x_6209_, 1, v___x_6207_);
return v___x_6209_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; 
v___x_6210_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6211_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6212_ = l_Lean_Expr_const___override(v___x_6211_, v___x_6210_);
return v___x_6212_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; 
v___x_6213_ = l_Lean_Nat_mkInstHAdd;
v___x_6214_ = l_Lean_Nat_mkType;
v___x_6215_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6216_ = l_Lean_mkApp4(v___x_6215_, v___x_6214_, v___x_6214_, v___x_6214_, v___x_6213_);
return v___x_6216_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6217_; 
v___x_6217_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6217_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; 
v___x_6223_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6224_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6225_ = l_Lean_Expr_const___override(v___x_6224_, v___x_6223_);
return v___x_6225_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; 
v___x_6226_ = l_Lean_Nat_mkInstHSub;
v___x_6227_ = l_Lean_Nat_mkType;
v___x_6228_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6229_ = l_Lean_mkApp4(v___x_6228_, v___x_6227_, v___x_6227_, v___x_6227_, v___x_6226_);
return v___x_6229_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6230_; 
v___x_6230_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6230_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; 
v___x_6236_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6237_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6238_ = l_Lean_Expr_const___override(v___x_6237_, v___x_6236_);
return v___x_6238_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; 
v___x_6239_ = l_Lean_Nat_mkInstHMul;
v___x_6240_ = l_Lean_Nat_mkType;
v___x_6241_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6242_ = l_Lean_mkApp4(v___x_6241_, v___x_6240_, v___x_6240_, v___x_6240_, v___x_6239_);
return v___x_6242_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6243_; 
v___x_6243_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6243_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6249_; lean_object* v___x_6250_; lean_object* v___x_6251_; 
v___x_6249_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6250_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6251_ = l_Lean_Expr_const___override(v___x_6250_, v___x_6249_);
return v___x_6251_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6252_ = l_Lean_Nat_mkInstHPow;
v___x_6253_ = l_Lean_Nat_mkType;
v___x_6254_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6255_ = l_Lean_mkApp4(v___x_6254_, v___x_6253_, v___x_6253_, v___x_6253_, v___x_6252_);
return v___x_6255_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6256_; 
v___x_6256_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6256_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; 
v___x_6261_ = lean_box(0);
v___x_6262_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6263_ = l_Lean_Expr_const___override(v___x_6262_, v___x_6261_);
return v___x_6263_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6264_){
_start:
{
lean_object* v___x_6265_; lean_object* v___x_6266_; 
v___x_6265_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6266_ = l_Lean_Expr_app___override(v___x_6265_, v_a_6264_);
return v___x_6266_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6267_, lean_object* v_b_6268_){
_start:
{
lean_object* v___x_6269_; lean_object* v___x_6270_; 
v___x_6269_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6270_ = l_Lean_mkAppB(v___x_6269_, v_a_6267_, v_b_6268_);
return v___x_6270_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6271_, lean_object* v_b_6272_){
_start:
{
lean_object* v___x_6273_; lean_object* v___x_6274_; 
v___x_6273_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6274_ = l_Lean_mkAppB(v___x_6273_, v_a_6271_, v_b_6272_);
return v___x_6274_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6275_, lean_object* v_b_6276_){
_start:
{
lean_object* v___x_6277_; lean_object* v___x_6278_; 
v___x_6277_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6278_ = l_Lean_mkAppB(v___x_6277_, v_a_6275_, v_b_6276_);
return v___x_6278_;
}
}
static lean_object* _init_l_Lean_mkNatDiv___closed__3(void){
_start:
{
lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; 
v___x_6284_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6285_ = ((lean_object*)(l_Lean_mkNatDiv___closed__2));
v___x_6286_ = l_Lean_Expr_const___override(v___x_6285_, v___x_6284_);
return v___x_6286_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatDiv(lean_object* v_a_6287_, lean_object* v_b_6288_){
_start:
{
lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; 
v___x_6289_ = lean_obj_once(&l_Lean_mkNatDiv___closed__3, &l_Lean_mkNatDiv___closed__3_once, _init_l_Lean_mkNatDiv___closed__3);
v___x_6290_ = l_Lean_Nat_mkType;
v___x_6291_ = l_Lean_Nat_mkInstHDiv;
v___x_6292_ = l_Lean_mkApp6(v___x_6289_, v___x_6290_, v___x_6290_, v___x_6290_, v___x_6291_, v_a_6287_, v_b_6288_);
return v___x_6292_;
}
}
static lean_object* _init_l_Lean_mkNatMod___closed__3(void){
_start:
{
lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; 
v___x_6298_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6299_ = ((lean_object*)(l_Lean_mkNatMod___closed__2));
v___x_6300_ = l_Lean_Expr_const___override(v___x_6299_, v___x_6298_);
return v___x_6300_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMod(lean_object* v_a_6301_, lean_object* v_b_6302_){
_start:
{
lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; 
v___x_6303_ = lean_obj_once(&l_Lean_mkNatMod___closed__3, &l_Lean_mkNatMod___closed__3_once, _init_l_Lean_mkNatMod___closed__3);
v___x_6304_ = l_Lean_Nat_mkType;
v___x_6305_ = l_Lean_Nat_mkInstHMod;
v___x_6306_ = l_Lean_mkApp6(v___x_6303_, v___x_6304_, v___x_6304_, v___x_6304_, v___x_6305_, v_a_6301_, v_b_6302_);
return v___x_6306_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6307_, lean_object* v_b_6308_){
_start:
{
lean_object* v___x_6309_; lean_object* v___x_6310_; 
v___x_6309_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6310_ = l_Lean_mkAppB(v___x_6309_, v_a_6307_, v_b_6308_);
return v___x_6310_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; 
v___x_6316_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6317_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6318_ = l_Lean_Expr_const___override(v___x_6317_, v___x_6316_);
return v___x_6318_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; 
v___x_6319_ = l_Lean_Nat_mkInstLE;
v___x_6320_ = l_Lean_Nat_mkType;
v___x_6321_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6322_ = l_Lean_mkAppB(v___x_6321_, v___x_6320_, v___x_6319_);
return v___x_6322_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6323_; 
v___x_6323_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6323_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6324_, lean_object* v_b_6325_){
_start:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; 
v___x_6326_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6327_ = l_Lean_mkAppB(v___x_6326_, v_a_6324_, v_b_6325_);
return v___x_6327_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6328_; lean_object* v___x_6329_; 
v___x_6328_ = lean_unsigned_to_nat(1u);
v___x_6329_ = l_Lean_Level_ofNat(v___x_6328_);
return v___x_6329_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; 
v___x_6330_ = lean_box(0);
v___x_6331_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6332_, 0, v___x_6331_);
lean_ctor_set(v___x_6332_, 1, v___x_6330_);
return v___x_6332_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6333_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6334_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6335_ = l_Lean_Expr_const___override(v___x_6334_, v___x_6333_);
return v___x_6335_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; 
v___x_6336_ = l_Lean_Nat_mkType;
v___x_6337_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6338_ = l_Lean_Expr_app___override(v___x_6337_, v___x_6336_);
return v___x_6338_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6339_; 
v___x_6339_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6339_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6340_, lean_object* v_b_6341_){
_start:
{
lean_object* v___x_6342_; lean_object* v___x_6343_; 
v___x_6342_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6343_ = l_Lean_mkAppB(v___x_6342_, v_a_6340_, v_b_6341_);
return v___x_6343_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6344_; lean_object* v___x_6345_; 
v___x_6344_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6345_ = l_Lean_Expr_sort___override(v___x_6344_);
return v___x_6345_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; 
v___x_6346_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6347_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6348_ = l_Lean_Expr_app___override(v___x_6347_, v___x_6346_);
return v___x_6348_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6349_; 
v___x_6349_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6349_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6350_, lean_object* v_b_6351_){
_start:
{
lean_object* v___x_6352_; lean_object* v___x_6353_; 
v___x_6352_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6353_ = l_Lean_mkAppB(v___x_6352_, v_a_6350_, v_b_6351_);
return v___x_6353_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; 
v___x_6357_ = lean_box(0);
v___x_6358_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6359_ = l_Lean_Expr_const___override(v___x_6358_, v___x_6357_);
return v___x_6359_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6360_; 
v___x_6360_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6360_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; 
v___x_6365_ = lean_box(0);
v___x_6366_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6367_ = l_Lean_Expr_const___override(v___x_6366_, v___x_6365_);
return v___x_6367_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6368_; 
v___x_6368_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6368_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; 
v___x_6373_ = lean_box(0);
v___x_6374_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6375_ = l_Lean_Expr_const___override(v___x_6374_, v___x_6373_);
return v___x_6375_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6376_; 
v___x_6376_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6376_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; 
v___x_6377_ = l_Lean_Int_mkInstAdd;
v___x_6378_ = l_Lean_Int_mkType;
v___x_6379_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6380_ = l_Lean_mkAppB(v___x_6379_, v___x_6378_, v___x_6377_);
return v___x_6380_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6381_; 
v___x_6381_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6381_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; 
v___x_6386_ = lean_box(0);
v___x_6387_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6388_ = l_Lean_Expr_const___override(v___x_6387_, v___x_6386_);
return v___x_6388_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6389_; 
v___x_6389_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6389_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6390_; lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; 
v___x_6390_ = l_Lean_Int_mkInstSub;
v___x_6391_ = l_Lean_Int_mkType;
v___x_6392_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6393_ = l_Lean_mkAppB(v___x_6392_, v___x_6391_, v___x_6390_);
return v___x_6393_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6394_; 
v___x_6394_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6394_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6399_; lean_object* v___x_6400_; lean_object* v___x_6401_; 
v___x_6399_ = lean_box(0);
v___x_6400_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6401_ = l_Lean_Expr_const___override(v___x_6400_, v___x_6399_);
return v___x_6401_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6402_; 
v___x_6402_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6402_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; lean_object* v___x_6406_; 
v___x_6403_ = l_Lean_Int_mkInstMul;
v___x_6404_ = l_Lean_Int_mkType;
v___x_6405_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6406_ = l_Lean_mkAppB(v___x_6405_, v___x_6404_, v___x_6403_);
return v___x_6406_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6407_; 
v___x_6407_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6407_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; 
v___x_6411_ = lean_box(0);
v___x_6412_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6413_ = l_Lean_Expr_const___override(v___x_6412_, v___x_6411_);
return v___x_6413_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6414_; 
v___x_6414_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6414_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; lean_object* v___x_6418_; 
v___x_6415_ = l_Lean_Int_mkInstDiv;
v___x_6416_ = l_Lean_Int_mkType;
v___x_6417_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6418_ = l_Lean_mkAppB(v___x_6417_, v___x_6416_, v___x_6415_);
return v___x_6418_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6419_; 
v___x_6419_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6419_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; 
v___x_6423_ = lean_box(0);
v___x_6424_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6425_ = l_Lean_Expr_const___override(v___x_6424_, v___x_6423_);
return v___x_6425_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6426_; 
v___x_6426_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6426_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; lean_object* v___x_6430_; 
v___x_6427_ = l_Lean_Int_mkInstMod;
v___x_6428_ = l_Lean_Int_mkType;
v___x_6429_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6430_ = l_Lean_mkAppB(v___x_6429_, v___x_6428_, v___x_6427_);
return v___x_6430_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6431_; 
v___x_6431_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6431_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; 
v___x_6436_ = lean_box(0);
v___x_6437_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6438_ = l_Lean_Expr_const___override(v___x_6437_, v___x_6436_);
return v___x_6438_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6439_; 
v___x_6439_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6439_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6440_; lean_object* v___x_6441_; lean_object* v___x_6442_; lean_object* v___x_6443_; 
v___x_6440_ = l_Lean_Int_mkInstPow;
v___x_6441_ = l_Lean_Int_mkType;
v___x_6442_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6443_ = l_Lean_mkAppB(v___x_6442_, v___x_6441_, v___x_6440_);
return v___x_6443_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6444_; 
v___x_6444_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6444_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6445_; lean_object* v___x_6446_; lean_object* v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; 
v___x_6445_ = l_Lean_Int_mkInstPowNat;
v___x_6446_ = l_Lean_Nat_mkType;
v___x_6447_ = l_Lean_Int_mkType;
v___x_6448_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6449_ = l_Lean_mkApp3(v___x_6448_, v___x_6447_, v___x_6446_, v___x_6445_);
return v___x_6449_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6450_; 
v___x_6450_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6450_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6455_; lean_object* v___x_6456_; lean_object* v___x_6457_; 
v___x_6455_ = lean_box(0);
v___x_6456_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6457_ = l_Lean_Expr_const___override(v___x_6456_, v___x_6455_);
return v___x_6457_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6458_; 
v___x_6458_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6458_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6463_; lean_object* v___x_6464_; lean_object* v___x_6465_; 
v___x_6463_ = lean_box(0);
v___x_6464_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6465_ = l_Lean_Expr_const___override(v___x_6464_, v___x_6463_);
return v___x_6465_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6466_; 
v___x_6466_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6466_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; 
v___x_6470_ = lean_box(0);
v___x_6471_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6472_ = l_Lean_Expr_const___override(v___x_6471_, v___x_6470_);
return v___x_6472_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6473_; 
v___x_6473_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6473_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; 
v___x_6474_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6475_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6476_ = l_Lean_Expr_const___override(v___x_6475_, v___x_6474_);
return v___x_6476_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; 
v___x_6477_ = l_Lean_Int_mkInstNeg;
v___x_6478_ = l_Lean_Int_mkType;
v___x_6479_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6480_ = l_Lean_mkAppB(v___x_6479_, v___x_6478_, v___x_6477_);
return v___x_6480_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6481_; 
v___x_6481_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6481_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; 
v___x_6482_ = l_Lean_Int_mkInstHAdd;
v___x_6483_ = l_Lean_Int_mkType;
v___x_6484_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6485_ = l_Lean_mkApp4(v___x_6484_, v___x_6483_, v___x_6483_, v___x_6483_, v___x_6482_);
return v___x_6485_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6486_; 
v___x_6486_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6486_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; 
v___x_6487_ = l_Lean_Int_mkInstHSub;
v___x_6488_ = l_Lean_Int_mkType;
v___x_6489_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6490_ = l_Lean_mkApp4(v___x_6489_, v___x_6488_, v___x_6488_, v___x_6488_, v___x_6487_);
return v___x_6490_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6491_; 
v___x_6491_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6491_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; 
v___x_6492_ = l_Lean_Int_mkInstHMul;
v___x_6493_ = l_Lean_Int_mkType;
v___x_6494_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6495_ = l_Lean_mkApp4(v___x_6494_, v___x_6493_, v___x_6493_, v___x_6493_, v___x_6492_);
return v___x_6495_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6496_; 
v___x_6496_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6496_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__0(void){
_start:
{
lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; 
v___x_6497_ = l_Lean_Int_mkInstHDiv;
v___x_6498_ = l_Lean_Int_mkType;
v___x_6499_ = lean_obj_once(&l_Lean_mkNatDiv___closed__3, &l_Lean_mkNatDiv___closed__3_once, _init_l_Lean_mkNatDiv___closed__3);
v___x_6500_ = l_Lean_mkApp4(v___x_6499_, v___x_6498_, v___x_6498_, v___x_6498_, v___x_6497_);
return v___x_6500_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6501_; 
v___x_6501_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__0, &l___private_Lean_Expr_0__Lean_intDivFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__0);
return v___x_6501_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__0(void){
_start:
{
lean_object* v___x_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; 
v___x_6502_ = l_Lean_Int_mkInstHMod;
v___x_6503_ = l_Lean_Int_mkType;
v___x_6504_ = lean_obj_once(&l_Lean_mkNatMod___closed__3, &l_Lean_mkNatMod___closed__3_once, _init_l_Lean_mkNatMod___closed__3);
v___x_6505_ = l_Lean_mkApp4(v___x_6504_, v___x_6503_, v___x_6503_, v___x_6503_, v___x_6502_);
return v___x_6505_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6506_; 
v___x_6506_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__0, &l___private_Lean_Expr_0__Lean_intModFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__0);
return v___x_6506_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; 
v___x_6507_ = l_Lean_Int_mkInstHPow;
v___x_6508_ = l_Lean_Nat_mkType;
v___x_6509_ = l_Lean_Int_mkType;
v___x_6510_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6511_ = l_Lean_mkApp4(v___x_6510_, v___x_6509_, v___x_6508_, v___x_6509_, v___x_6507_);
return v___x_6511_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6512_; 
v___x_6512_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6512_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; 
v___x_6518_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6519_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6520_ = l_Lean_Expr_const___override(v___x_6519_, v___x_6518_);
return v___x_6520_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; lean_object* v___x_6524_; 
v___x_6521_ = l_Lean_Int_mkInstNatCast;
v___x_6522_ = l_Lean_Int_mkType;
v___x_6523_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6524_ = l_Lean_mkAppB(v___x_6523_, v___x_6522_, v___x_6521_);
return v___x_6524_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6525_; 
v___x_6525_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6525_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6526_){
_start:
{
lean_object* v___x_6527_; lean_object* v___x_6528_; 
v___x_6527_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6528_ = l_Lean_Expr_app___override(v___x_6527_, v_a_6526_);
return v___x_6528_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6529_, lean_object* v_b_6530_){
_start:
{
lean_object* v___x_6531_; lean_object* v___x_6532_; 
v___x_6531_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6532_ = l_Lean_mkAppB(v___x_6531_, v_a_6529_, v_b_6530_);
return v___x_6532_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6533_, lean_object* v_b_6534_){
_start:
{
lean_object* v___x_6535_; lean_object* v___x_6536_; 
v___x_6535_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6536_ = l_Lean_mkAppB(v___x_6535_, v_a_6533_, v_b_6534_);
return v___x_6536_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6537_, lean_object* v_b_6538_){
_start:
{
lean_object* v___x_6539_; lean_object* v___x_6540_; 
v___x_6539_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6540_ = l_Lean_mkAppB(v___x_6539_, v_a_6537_, v_b_6538_);
return v___x_6540_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6541_, lean_object* v_b_6542_){
_start:
{
lean_object* v___x_6543_; lean_object* v___x_6544_; 
v___x_6543_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6544_ = l_Lean_mkAppB(v___x_6543_, v_a_6541_, v_b_6542_);
return v___x_6544_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6545_, lean_object* v_b_6546_){
_start:
{
lean_object* v___x_6547_; lean_object* v___x_6548_; 
v___x_6547_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6548_ = l_Lean_mkAppB(v___x_6547_, v_a_6545_, v_b_6546_);
return v___x_6548_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6549_){
_start:
{
lean_object* v___x_6550_; lean_object* v___x_6551_; 
v___x_6550_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6551_ = l_Lean_Expr_app___override(v___x_6550_, v_a_6549_);
return v___x_6551_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6552_, lean_object* v_b_6553_){
_start:
{
lean_object* v___x_6554_; lean_object* v___x_6555_; 
v___x_6554_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6555_ = l_Lean_mkAppB(v___x_6554_, v_a_6552_, v_b_6553_);
return v___x_6555_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6556_; lean_object* v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; 
v___x_6556_ = l_Lean_Int_mkInstLE;
v___x_6557_ = l_Lean_Int_mkType;
v___x_6558_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6559_ = l_Lean_mkAppB(v___x_6558_, v___x_6557_, v___x_6556_);
return v___x_6559_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6560_; 
v___x_6560_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6561_, lean_object* v_b_6562_){
_start:
{
lean_object* v___x_6563_; lean_object* v___x_6564_; 
v___x_6563_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6564_ = l_Lean_mkAppB(v___x_6563_, v_a_6561_, v_b_6562_);
return v___x_6564_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; 
v___x_6570_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6571_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6572_ = l_Lean_Expr_const___override(v___x_6571_, v___x_6570_);
return v___x_6572_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6573_; lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; 
v___x_6573_ = l_Lean_Int_mkInstLT;
v___x_6574_ = l_Lean_Int_mkType;
v___x_6575_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6576_ = l_Lean_mkAppB(v___x_6575_, v___x_6574_, v___x_6573_);
return v___x_6576_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6577_; 
v___x_6577_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6577_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6578_, lean_object* v_b_6579_){
_start:
{
lean_object* v___x_6580_; lean_object* v___x_6581_; 
v___x_6580_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6581_ = l_Lean_mkAppB(v___x_6580_, v_a_6578_, v_b_6579_);
return v___x_6581_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6582_; lean_object* v___x_6583_; lean_object* v___x_6584_; 
v___x_6582_ = l_Lean_Int_mkType;
v___x_6583_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6584_ = l_Lean_Expr_app___override(v___x_6583_, v___x_6582_);
return v___x_6584_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6585_; 
v___x_6585_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6585_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6586_, lean_object* v_b_6587_){
_start:
{
lean_object* v___x_6588_; lean_object* v___x_6589_; 
v___x_6588_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6589_ = l_Lean_mkAppB(v___x_6588_, v_a_6586_, v_b_6587_);
return v___x_6589_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; 
v___x_6595_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6596_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6597_ = l_Lean_Expr_const___override(v___x_6596_, v___x_6595_);
return v___x_6597_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; 
v___x_6602_ = lean_box(0);
v___x_6603_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6604_ = l_Lean_Expr_const___override(v___x_6603_, v___x_6602_);
return v___x_6604_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6605_, lean_object* v_b_6606_){
_start:
{
lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; 
v___x_6607_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6608_ = l_Lean_Int_mkType;
v___x_6609_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6610_ = l_Lean_mkApp4(v___x_6607_, v___x_6608_, v___x_6609_, v_a_6605_, v_b_6606_);
return v___x_6610_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6614_; lean_object* v___x_6615_; lean_object* v___x_6616_; 
v___x_6614_ = lean_box(0);
v___x_6615_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6616_ = l_Lean_Expr_const___override(v___x_6615_, v___x_6614_);
return v___x_6616_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6617_; lean_object* v___x_6618_; 
v___x_6617_ = lean_unsigned_to_nat(0u);
v___x_6618_ = lean_nat_to_int(v___x_6617_);
return v___x_6618_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6619_){
_start:
{
lean_object* v___x_6620_; lean_object* v_r_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; lean_object* v_r_6626_; lean_object* v___x_6627_; uint8_t v___x_6628_; 
v___x_6620_ = lean_nat_abs(v_n_6619_);
v_r_6621_ = l_Lean_mkRawNatLit(v___x_6620_);
v___x_6622_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6623_ = l_Lean_Int_mkType;
v___x_6624_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6621_);
v___x_6625_ = l_Lean_Expr_app___override(v___x_6624_, v_r_6621_);
v_r_6626_ = l_Lean_mkApp3(v___x_6622_, v___x_6623_, v_r_6621_, v___x_6625_);
v___x_6627_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6628_ = lean_int_dec_lt(v_n_6619_, v___x_6627_);
if (v___x_6628_ == 0)
{
return v_r_6626_;
}
else
{
lean_object* v___x_6629_; 
v___x_6629_ = l_Lean_mkIntNeg(v_r_6626_);
return v___x_6629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6630_){
_start:
{
lean_object* v_res_6631_; 
v_res_6631_ = l_Lean_mkIntLit(v_n_6630_);
lean_dec(v_n_6630_);
return v_res_6631_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6636_; lean_object* v___x_6637_; 
v___x_6636_ = lean_box(0);
v___x_6637_ = l_Lean_Level_succ___override(v___x_6636_);
return v___x_6637_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; 
v___x_6638_ = lean_box(0);
v___x_6639_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6640_, 0, v___x_6639_);
lean_ctor_set(v___x_6640_, 1, v___x_6638_);
return v___x_6640_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___x_6643_; 
v___x_6641_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6642_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6643_ = l_Lean_Expr_const___override(v___x_6642_, v___x_6641_);
return v___x_6643_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; 
v___x_6646_ = lean_box(0);
v___x_6647_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6648_ = l_Lean_Expr_const___override(v___x_6647_, v___x_6646_);
return v___x_6648_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; 
v___x_6649_ = lean_box(0);
v___x_6650_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6651_ = l_Lean_Expr_const___override(v___x_6650_, v___x_6649_);
return v___x_6651_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6652_; lean_object* v___x_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; 
v___x_6652_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6653_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6654_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6655_ = l_Lean_mkAppB(v___x_6654_, v___x_6653_, v___x_6652_);
return v___x_6655_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6656_; 
v___x_6656_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6656_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; 
v___x_6657_ = lean_box(0);
v___x_6658_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__2));
v___x_6659_ = l_Lean_Expr_const___override(v___x_6658_, v___x_6657_);
return v___x_6659_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; lean_object* v___x_6663_; 
v___x_6660_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6661_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6662_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6663_ = l_Lean_mkAppB(v___x_6662_, v___x_6661_, v___x_6660_);
return v___x_6663_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6664_; 
v___x_6664_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6664_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6668_; lean_object* v___x_6669_; lean_object* v___x_6670_; 
v___x_6668_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6669_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6670_ = l_Lean_Expr_const___override(v___x_6669_, v___x_6668_);
return v___x_6670_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; lean_object* v___x_6674_; 
v___x_6671_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6672_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6673_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6674_ = l_Lean_mkApp3(v___x_6673_, v___x_6672_, v___x_6671_, v___x_6671_);
return v___x_6674_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; 
v___x_6675_ = l_Lean_reflBoolTrue;
v___x_6676_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6677_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6678_ = l_Lean_mkAppB(v___x_6677_, v___x_6676_, v___x_6675_);
return v___x_6678_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6679_; 
v___x_6679_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6679_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; 
v___x_6680_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6681_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6682_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6683_ = l_Lean_mkApp3(v___x_6682_, v___x_6681_, v___x_6680_, v___x_6680_);
return v___x_6683_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; 
v___x_6684_ = l_Lean_reflBoolFalse;
v___x_6685_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6686_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6687_ = l_Lean_mkAppB(v___x_6686_, v___x_6685_, v___x_6684_);
return v___x_6687_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6688_; 
v___x_6688_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6688_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6691_; lean_object* v___x_6692_; lean_object* v___x_6693_; lean_object* v___x_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; 
v___x_6691_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6692_ = lean_unsigned_to_nat(9u);
v___x_6693_ = lean_unsigned_to_nat(2537u);
v___x_6694_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6695_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6696_ = l_mkPanicMessageWithDecl(v___x_6695_, v___x_6694_, v___x_6693_, v___x_6692_, v___x_6691_);
return v___x_6696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6697_, lean_object* v_declName_6698_){
_start:
{
switch(lean_obj_tag(v_e_6697_))
{
case 5:
{
lean_object* v_fn_6699_; lean_object* v_arg_6700_; lean_object* v___x_6701_; lean_object* v___x_6702_; 
v_fn_6699_ = lean_ctor_get(v_e_6697_, 0);
lean_inc_ref(v_fn_6699_);
v_arg_6700_ = lean_ctor_get(v_e_6697_, 1);
lean_inc_ref(v_arg_6700_);
lean_dec_ref_known(v_e_6697_, 2);
v___x_6701_ = l_Lean_Expr_replaceFn(v_fn_6699_, v_declName_6698_);
v___x_6702_ = l_Lean_Expr_app___override(v___x_6701_, v_arg_6700_);
return v___x_6702_;
}
case 4:
{
lean_object* v_us_6703_; lean_object* v___x_6704_; 
v_us_6703_ = lean_ctor_get(v_e_6697_, 1);
lean_inc(v_us_6703_);
lean_dec_ref_known(v_e_6697_, 2);
v___x_6704_ = l_Lean_Expr_const___override(v_declName_6698_, v_us_6703_);
return v___x_6704_;
}
default: 
{
lean_object* v___x_6705_; lean_object* v___x_6706_; 
lean_dec(v_declName_6698_);
lean_dec_ref(v_e_6697_);
v___x_6705_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6706_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6705_);
return v___x_6706_;
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
