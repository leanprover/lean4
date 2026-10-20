// Lean compiler output
// Module: LeanExport.Basic
// Imports: public import Lean public import Std.Data.HashMap.Basic
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Level_param___override(lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_instReprDataValue_repr(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
extern lean_object* l_Lean_githash;
extern lean_object* l_Lean_versionString;
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_IO_println___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "implicit"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "strictImplicit"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instImplicit"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(uint8_t);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___boxed(lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___boxed(lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ctor"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(uint8_t);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___boxed(lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unsafe"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "safe"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(uint8_t);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__Lean_KVMap_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_KVMap_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__0;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__1;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__2;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__3;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__4;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__5;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__6;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__7;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__8;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__9;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__10;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__11;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__12;
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_M_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--ignore-missing"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__2___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__2___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__2___boxed(lean_object*);
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "--export-mdata"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__0___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__0___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "--export-unsafe"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__1___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__1___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object*);
static const lean_closure_object l_LeanExport_initState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_LeanExport_initState___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_LeanExport_initState___closed__0 = (const lean_object*)&l_LeanExport_initState___closed__0_value;
LEAN_EXPORT lean_object* l_LeanExport_initState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_initState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LeanExport.Basic"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.LeanExport.Basic.0.LeanExport.dumpName"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pre"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "il"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "imax"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "param"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.LeanExport.Basic.0.LeanExport.dumpLevel"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "_private.LeanExport.Basic.0.LeanExport.removeMData"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "LeanExport.dumpConstant"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 135, .m_capacity = 135, .m_length = 134, .m_data = "assertion violation: ((!ctorVal.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.1873.0 ).exportUnsafe)\n          "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Expected a `ConstantInfo.ctorInfo`."};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 131, .m_data = "assertion violation: ((!recVal.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.2114.0 ).exportUnsafe)\n        "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "expected a `constantinfo.recinfo`."};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_LeanExport_dumpExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpExpr___closed__0;
static lean_once_cell_t l_LeanExport_dumpExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpExpr___closed__1;
static const lean_string_object l_LeanExport_dumpExprAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ie"};
static const lean_object* l_LeanExport_dumpExprAux___closed__0 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__0_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bvar"};
static const lean_object* l_LeanExport_dumpExprAux___closed__1 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__1_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sort"};
static const lean_object* l_LeanExport_dumpExprAux___closed__2 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__2_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_LeanExport_dumpExprAux___closed__3 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "us"};
static const lean_object* l_LeanExport_dumpExprAux___closed__4 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__4_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_LeanExport_dumpExprAux___closed__5 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__5_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "fn"};
static const lean_object* l_LeanExport_dumpExprAux___closed__6 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__6_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_LeanExport_dumpExprAux___closed__7 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__7_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lam"};
static const lean_object* l_LeanExport_dumpExprAux___closed__8 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__8_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* l_LeanExport_dumpExprAux___closed__9 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__9_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binderInfo"};
static const lean_object* l_LeanExport_dumpExprAux___closed__10 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__10_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "forallE"};
static const lean_object* l_LeanExport_dumpExprAux___closed__11 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__11_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "letE"};
static const lean_object* l_LeanExport_dumpExprAux___closed__12 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__12_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_LeanExport_dumpExprAux___closed__13 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__13_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nondep"};
static const lean_object* l_LeanExport_dumpExprAux___closed__14 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__14_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(lean_object*, lean_object*);
static const lean_string_object l_LeanExport_dumpExprAux___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natVal"};
static const lean_object* l_LeanExport_dumpExprAux___closed__15 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__15_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofList"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1_value),LEAN_SCALAR_PTR_LITERAL(118, 246, 177, 142, 179, 9, 199, 233)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(lean_object*, lean_object*);
static const lean_string_object l_LeanExport_dumpExprAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strVal"};
static const lean_object* l_LeanExport_dumpExprAux___closed__16 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__16_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mdata"};
static const lean_object* l_LeanExport_dumpExprAux___closed__17 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__17_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_LeanExport_dumpExprAux___closed__18 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__18_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "expr"};
static const lean_object* l_LeanExport_dumpExprAux___closed__19 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__19_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_LeanExport_dumpExprAux___closed__20 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__20_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeName"};
static const lean_object* l_LeanExport_dumpExprAux___closed__21 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__21_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l_LeanExport_dumpExprAux___closed__22 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__22_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "struct"};
static const lean_object* l_LeanExport_dumpExprAux___closed__23 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__23_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "cannot export free variables or metavariables"};
static const lean_object* l_LeanExport_dumpExprAux___closed__25 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__25_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "LeanExport.dumpExprAux"};
static const lean_object* l_LeanExport_dumpExprAux___closed__24 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__24_value;
static lean_once_cell_t l_LeanExport_dumpExprAux___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpExprAux___closed__26;
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "levelParams"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numParams"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numIndices"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ctors"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numNested"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isRec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "isReflexive"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isUnsafe"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "induct"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cidx"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numFields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nfields"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numMotives"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numMinors"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rules"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_LeanExport_dumpConstant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inductive"};
static const lean_object* l_LeanExport_dumpConstant___closed__0 = (const lean_object*)&l_LeanExport_dumpConstant___closed__0_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "types"};
static const lean_object* l_LeanExport_dumpConstant___closed__1 = (const lean_object*)&l_LeanExport_dumpConstant___closed__1_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "recs"};
static const lean_object* l_LeanExport_dumpConstant___closed__2 = (const lean_object*)&l_LeanExport_dumpConstant___closed__2_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "axiom"};
static const lean_object* l_LeanExport_dumpConstant___closed__3 = (const lean_object*)&l_LeanExport_dumpConstant___closed__3_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_LeanExport_dumpConstant___closed__4 = (const lean_object*)&l_LeanExport_dumpConstant___closed__4_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hints"};
static const lean_object* l_LeanExport_dumpConstant___closed__5 = (const lean_object*)&l_LeanExport_dumpConstant___closed__5_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "safety"};
static const lean_object* l_LeanExport_dumpConstant___closed__6 = (const lean_object*)&l_LeanExport_dumpConstant___closed__6_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l_LeanExport_dumpConstant___closed__7 = (const lean_object*)&l_LeanExport_dumpConstant___closed__7_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_LeanExport_dumpConstant___closed__8 = (const lean_object*)&l_LeanExport_dumpConstant___closed__8_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__8_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_LeanExport_dumpConstant___closed__9 = (const lean_object*)&l_LeanExport_dumpConstant___closed__9_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l_LeanExport_dumpConstant___closed__10 = (const lean_object*)&l_LeanExport_dumpConstant___closed__10_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_LeanExport_dumpConstant___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__15_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(150, 213, 121, 152, 109, 27, 137, 60)}};
static const lean_object* l_LeanExport_dumpConstant___closed__15 = (const lean_object*)&l_LeanExport_dumpConstant___closed__15_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_LeanExport_dumpConstant___closed__16 = (const lean_object*)&l_LeanExport_dumpConstant___closed__16_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_LeanExport_dumpConstant___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__14_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(91, 125, 38, 34, 222, 200, 201, 80)}};
static const lean_object* l_LeanExport_dumpConstant___closed__14 = (const lean_object*)&l_LeanExport_dumpConstant___closed__14_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__14_value),((lean_object*)&l_LeanExport_dumpConstant___closed__16_value)}};
static const lean_object* l_LeanExport_dumpConstant___closed__17 = (const lean_object*)&l_LeanExport_dumpConstant___closed__17_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_LeanExport_dumpConstant___closed__12 = (const lean_object*)&l_LeanExport_dumpConstant___closed__12_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_LeanExport_dumpConstant___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__13_value_aux_0),((lean_object*)&l_LeanExport_dumpConstant___closed__12_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l_LeanExport_dumpConstant___closed__13 = (const lean_object*)&l_LeanExport_dumpConstant___closed__13_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__13_value),((lean_object*)&l_LeanExport_dumpConstant___closed__17_value)}};
static const lean_object* l_LeanExport_dumpConstant___closed__18 = (const lean_object*)&l_LeanExport_dumpConstant___closed__18_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l_LeanExport_dumpConstant___closed__11 = (const lean_object*)&l_LeanExport_dumpConstant___closed__11_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__11_value),((lean_object*)&l_LeanExport_dumpConstant___closed__18_value)}};
static const lean_object* l_LeanExport_dumpConstant___closed__19 = (const lean_object*)&l_LeanExport_dumpConstant___closed__19_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Constant "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " not found in environment."};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_LeanExport_dumpConstant___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_LeanExport_dumpConstant___closed__20 = (const lean_object*)&l_LeanExport_dumpConstant___closed__20_value;
static lean_once_cell_t l_LeanExport_dumpConstant___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpConstant___closed__21;
static lean_once_cell_t l_LeanExport_dumpConstant___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpConstant___closed__22;
static const lean_closure_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 367, .m_capacity = 367, .m_length = 366, .m_data = "assertion violation: ctorVals.size == 0\n\n    /- We dump the constructor dependencies (which will not include the inductives in this block since we've\n    added the names to `visitedConstants`) before actually outputting anything in this inductive block to\n    ensure e.g. the `LT` in `Fin.mk` is dumped before this inductive block appears in the export file. -/\n    "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 127, .m_capacity = 127, .m_length = 126, .m_data = "assertion violation: ((!val.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.1797.0 ).exportUnsafe)\n      "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "githash"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lean4export"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "3.1.0"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "exporter"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "format"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata;
static lean_once_cell_t l_LeanExport_dumpMetadata___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpMetadata___redArg___closed__0;
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg(lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(uint8_t v_x_13_){
_start:
{
switch(v_x_13_)
{
case 0:
{
lean_object* v___x_14_; 
v___x_14_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1));
return v___x_14_;
}
case 1:
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3));
return v___x_15_;
}
case 2:
{
lean_object* v___x_16_; 
v___x_16_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5));
return v___x_16_;
}
default: 
{
lean_object* v___x_17_; 
v___x_17_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7));
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___boxed(lean_object* v_x_18_){
_start:
{
uint8_t v_x_64__boxed_19_; lean_object* v_res_20_; 
v_x_64__boxed_19_ = lean_unbox(v_x_18_);
v_res_20_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_x_64__boxed_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(lean_object* v_x_28_){
_start:
{
switch(lean_obj_tag(v_x_28_))
{
case 0:
{
lean_object* v___x_29_; 
v___x_29_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1));
return v___x_29_;
}
case 1:
{
lean_object* v___x_30_; 
v___x_30_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3));
return v___x_30_;
}
default: 
{
uint32_t v_a_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_a_31_ = lean_ctor_get_uint32(v_x_28_, 0);
v___x_32_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4));
v___x_33_ = lean_uint32_to_nat(v_a_31_);
v___x_34_ = l_Lean_JsonNumber_fromNat(v___x_33_);
v___x_35_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_32_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
v___x_37_ = lean_box(0);
v___x_38_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_36_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = l_Lean_Json_mkObj(v___x_38_);
lean_dec_ref_known(v___x_38_, 2);
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___boxed(lean_object* v_x_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(v_x_40_);
lean_dec(v_x_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(uint8_t v_x_54_){
_start:
{
switch(v_x_54_)
{
case 0:
{
lean_object* v___x_55_; 
v___x_55_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1));
return v___x_55_;
}
case 1:
{
lean_object* v___x_56_; 
v___x_56_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3));
return v___x_56_;
}
case 2:
{
lean_object* v___x_57_; 
v___x_57_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5));
return v___x_57_;
}
default: 
{
lean_object* v___x_58_; 
v___x_58_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7));
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___boxed(lean_object* v_x_59_){
_start:
{
uint8_t v_x_64__boxed_60_; lean_object* v_res_61_; 
v_x_64__boxed_60_ = lean_unbox(v_x_59_);
v_res_61_ = l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(v_x_64__boxed_60_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(uint8_t v_x_71_){
_start:
{
switch(v_x_71_)
{
case 0:
{
lean_object* v___x_72_; 
v___x_72_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1));
return v___x_72_;
}
case 1:
{
lean_object* v___x_73_; 
v___x_73_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3));
return v___x_73_;
}
default: 
{
lean_object* v___x_74_; 
v___x_74_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5));
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___boxed(lean_object* v_x_75_){
_start:
{
uint8_t v_x_49__boxed_76_; lean_object* v_res_77_; 
v_x_49__boxed_76_ = lean_unbox(v_x_75_);
v_res_77_ = l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(v_x_49__boxed_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__Lean_KVMap_toJson_spec__0(lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
if (lean_obj_tag(v_a_78_) == 0)
{
lean_object* v___x_80_; 
v___x_80_ = l_List_reverse___redArg(v_a_79_);
return v___x_80_;
}
else
{
lean_object* v_head_81_; lean_object* v_tail_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_106_; 
v_head_81_ = lean_ctor_get(v_a_78_, 0);
v_tail_82_ = lean_ctor_get(v_a_78_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_a_78_);
if (v_isSharedCheck_106_ == 0)
{
v___x_84_ = v_a_78_;
v_isShared_85_ = v_isSharedCheck_106_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_tail_82_);
lean_inc(v_head_81_);
lean_dec(v_a_78_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_106_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_fst_86_; lean_object* v_snd_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_105_; 
v_fst_86_ = lean_ctor_get(v_head_81_, 0);
v_snd_87_ = lean_ctor_get(v_head_81_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_head_81_);
if (v_isSharedCheck_105_ == 0)
{
v___x_89_ = v_head_81_;
v_isShared_90_ = v_isSharedCheck_105_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_snd_87_);
lean_inc(v_fst_86_);
lean_dec(v_head_81_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_105_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_91_ = 1;
v___x_92_ = l_Lean_Name_toString(v_fst_86_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = l_Lean_instReprDataValue_repr(v_snd_87_, v___x_93_);
v___x_95_ = l_Std_Format_defWidth;
v___x_96_ = l_Std_Format_pretty(v___x_94_, v___x_95_, v___x_93_, v___x_93_);
v___x_97_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v___x_97_);
lean_ctor_set(v___x_89_, 0, v___x_92_);
v___x_99_ = v___x_89_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_97_);
v___x_99_ = v_reuseFailAlloc_104_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_101_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v_a_79_);
lean_ctor_set(v___x_84_, 0, v___x_99_);
v___x_101_ = v___x_84_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_99_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_a_79_);
v___x_101_ = v_reuseFailAlloc_103_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
v_a_78_ = v_tail_82_;
v_a_79_ = v___x_101_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_KVMap_toJson(lean_object* v_kvs_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_box(0);
v___x_109_ = l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__Lean_KVMap_toJson_spec__0(v_kvs_107_, v___x_108_);
v___x_110_ = l_Lean_Json_mkObj(v___x_109_);
lean_dec(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(lean_object* v_a_111_, lean_object* v_b_112_, lean_object* v_x_113_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
lean_dec(v_b_112_);
lean_dec(v_a_111_);
return v_x_113_;
}
else
{
lean_object* v_key_114_; lean_object* v_value_115_; lean_object* v_tail_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_128_; 
v_key_114_ = lean_ctor_get(v_x_113_, 0);
v_value_115_ = lean_ctor_get(v_x_113_, 1);
v_tail_116_ = lean_ctor_get(v_x_113_, 2);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_113_);
if (v_isSharedCheck_128_ == 0)
{
v___x_118_ = v_x_113_;
v_isShared_119_ = v_isSharedCheck_128_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_tail_116_);
lean_inc(v_value_115_);
lean_inc(v_key_114_);
lean_dec(v_x_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_128_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
uint8_t v___x_120_; 
v___x_120_ = lean_name_eq(v_key_114_, v_a_111_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_111_, v_b_112_, v_tail_116_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 2, v___x_121_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_key_114_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_value_115_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
else
{
lean_object* v___x_126_; 
lean_dec(v_value_115_);
lean_dec(v_key_114_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_b_112_);
lean_ctor_set(v___x_118_, 0, v_a_111_);
v___x_126_ = v___x_118_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_111_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_b_112_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_tail_116_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
return v_x_129_;
}
else
{
lean_object* v_key_131_; lean_object* v_value_132_; lean_object* v_tail_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_159_; 
v_key_131_ = lean_ctor_get(v_x_130_, 0);
v_value_132_ = lean_ctor_get(v_x_130_, 1);
v_tail_133_ = lean_ctor_get(v_x_130_, 2);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_159_ == 0)
{
v___x_135_ = v_x_130_;
v_isShared_136_ = v_isSharedCheck_159_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_tail_133_);
lean_inc(v_value_132_);
lean_inc(v_key_131_);
lean_dec(v_x_130_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_159_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; uint64_t v___y_139_; 
v___x_137_ = lean_array_get_size(v_x_129_);
if (lean_obj_tag(v_key_131_) == 0)
{
uint64_t v___x_157_; 
v___x_157_ = 1723ULL;
v___y_139_ = v___x_157_;
goto v___jp_138_;
}
else
{
uint64_t v_hash_158_; 
v_hash_158_ = lean_ctor_get_uint64(v_key_131_, sizeof(void*)*2);
v___y_139_ = v_hash_158_;
goto v___jp_138_;
}
v___jp_138_:
{
uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v_fold_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_140_ = 32ULL;
v___x_141_ = lean_uint64_shift_right(v___y_139_, v___x_140_);
v_fold_142_ = lean_uint64_xor(v___y_139_, v___x_141_);
v___x_143_ = 16ULL;
v___x_144_ = lean_uint64_shift_right(v_fold_142_, v___x_143_);
v___x_145_ = lean_uint64_xor(v_fold_142_, v___x_144_);
v___x_146_ = lean_uint64_to_usize(v___x_145_);
v___x_147_ = lean_usize_of_nat(v___x_137_);
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_sub(v___x_147_, v___x_148_);
v___x_150_ = lean_usize_land(v___x_146_, v___x_149_);
v___x_151_ = lean_array_uget_borrowed(v_x_129_, v___x_150_);
lean_inc(v___x_151_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 2, v___x_151_);
v___x_153_ = v___x_135_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_key_131_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_value_132_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v___x_151_);
v___x_153_ = v_reuseFailAlloc_156_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = lean_array_uset(v_x_129_, v___x_150_, v___x_153_);
v_x_129_ = v___x_154_;
v_x_130_ = v_tail_133_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(lean_object* v_i_160_, lean_object* v_source_161_, lean_object* v_target_162_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_array_get_size(v_source_161_);
v___x_164_ = lean_nat_dec_lt(v_i_160_, v___x_163_);
if (v___x_164_ == 0)
{
lean_dec_ref(v_source_161_);
lean_dec(v_i_160_);
return v_target_162_;
}
else
{
lean_object* v_es_165_; lean_object* v___x_166_; lean_object* v_source_167_; lean_object* v_target_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_es_165_ = lean_array_fget(v_source_161_, v_i_160_);
v___x_166_ = lean_box(0);
v_source_167_ = lean_array_fset(v_source_161_, v_i_160_, v___x_166_);
v_target_168_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(v_target_162_, v_es_165_);
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_add(v_i_160_, v___x_169_);
lean_dec(v_i_160_);
v_i_160_ = v___x_170_;
v_source_161_ = v_source_167_;
v_target_162_ = v_target_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(lean_object* v_data_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_nbuckets_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_173_ = lean_array_get_size(v_data_172_);
v___x_174_ = lean_unsigned_to_nat(2u);
v_nbuckets_175_ = lean_nat_mul(v___x_173_, v___x_174_);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_box(0);
v___x_178_ = lean_mk_array(v_nbuckets_175_, v___x_177_);
v___x_179_ = lean_array_propagate_mark(v_data_172_, v___x_178_);
v___x_180_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(v___x_176_, v_data_172_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(lean_object* v_a_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
uint8_t v___x_183_; 
v___x_183_ = 0;
return v___x_183_;
}
else
{
lean_object* v_key_184_; lean_object* v_tail_185_; uint8_t v___x_186_; 
v_key_184_ = lean_ctor_get(v_x_182_, 0);
v_tail_185_ = lean_ctor_get(v_x_182_, 2);
v___x_186_ = lean_name_eq(v_key_184_, v_a_181_);
if (v___x_186_ == 0)
{
v_x_182_ = v_tail_185_;
goto _start;
}
else
{
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg___boxed(lean_object* v_a_188_, lean_object* v_x_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_188_, v_x_189_);
lean_dec(v_x_189_);
lean_dec(v_a_188_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(lean_object* v_m_192_, lean_object* v_a_193_, lean_object* v_b_194_){
_start:
{
lean_object* v_size_195_; lean_object* v_buckets_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_242_; 
v_size_195_ = lean_ctor_get(v_m_192_, 0);
v_buckets_196_ = lean_ctor_get(v_m_192_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_m_192_);
if (v_isSharedCheck_242_ == 0)
{
v___x_198_ = v_m_192_;
v_isShared_199_ = v_isSharedCheck_242_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_buckets_196_);
lean_inc(v_size_195_);
lean_dec(v_m_192_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_242_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; uint64_t v___y_202_; 
v___x_200_ = lean_array_get_size(v_buckets_196_);
if (lean_obj_tag(v_a_193_) == 0)
{
uint64_t v___x_240_; 
v___x_240_ = 1723ULL;
v___y_202_ = v___x_240_;
goto v___jp_201_;
}
else
{
uint64_t v_hash_241_; 
v_hash_241_ = lean_ctor_get_uint64(v_a_193_, sizeof(void*)*2);
v___y_202_ = v_hash_241_;
goto v___jp_201_;
}
v___jp_201_:
{
uint64_t v___x_203_; uint64_t v___x_204_; uint64_t v_fold_205_; uint64_t v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; size_t v___x_209_; size_t v___x_210_; size_t v___x_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v_bkt_214_; uint8_t v___x_215_; 
v___x_203_ = 32ULL;
v___x_204_ = lean_uint64_shift_right(v___y_202_, v___x_203_);
v_fold_205_ = lean_uint64_xor(v___y_202_, v___x_204_);
v___x_206_ = 16ULL;
v___x_207_ = lean_uint64_shift_right(v_fold_205_, v___x_206_);
v___x_208_ = lean_uint64_xor(v_fold_205_, v___x_207_);
v___x_209_ = lean_uint64_to_usize(v___x_208_);
v___x_210_ = lean_usize_of_nat(v___x_200_);
v___x_211_ = ((size_t)1ULL);
v___x_212_ = lean_usize_sub(v___x_210_, v___x_211_);
v___x_213_ = lean_usize_land(v___x_209_, v___x_212_);
v_bkt_214_ = lean_array_uget_borrowed(v_buckets_196_, v___x_213_);
v___x_215_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_193_, v_bkt_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v_size_x27_217_; lean_object* v___x_218_; lean_object* v_buckets_x27_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v_size_x27_217_ = lean_nat_add(v_size_195_, v___x_216_);
lean_dec(v_size_195_);
lean_inc(v_bkt_214_);
v___x_218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_218_, 0, v_a_193_);
lean_ctor_set(v___x_218_, 1, v_b_194_);
lean_ctor_set(v___x_218_, 2, v_bkt_214_);
v_buckets_x27_219_ = lean_array_uset(v_buckets_196_, v___x_213_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(4u);
v___x_221_ = lean_nat_mul(v_size_x27_217_, v___x_220_);
v___x_222_ = lean_unsigned_to_nat(3u);
v___x_223_ = lean_nat_div(v___x_221_, v___x_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_array_get_size(v_buckets_x27_219_);
v___x_225_ = lean_nat_dec_le(v___x_223_, v___x_224_);
lean_dec(v___x_223_);
if (v___x_225_ == 0)
{
lean_object* v_val_226_; lean_object* v___x_228_; 
v_val_226_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(v_buckets_x27_219_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v_val_226_);
lean_ctor_set(v___x_198_, 0, v_size_x27_217_);
v___x_228_ = v___x_198_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_size_x27_217_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_val_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
else
{
lean_object* v___x_231_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v_buckets_x27_219_);
lean_ctor_set(v___x_198_, 0, v_size_x27_217_);
v___x_231_ = v___x_198_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_size_x27_217_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_buckets_x27_219_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
else
{
lean_object* v___x_233_; lean_object* v_buckets_x27_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
lean_inc(v_bkt_214_);
v___x_233_ = lean_box(0);
v_buckets_x27_234_ = lean_array_uset(v_buckets_196_, v___x_213_, v___x_233_);
v___x_235_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_193_, v_b_194_, v_bkt_214_);
v___x_236_ = lean_array_uset(v_buckets_x27_234_, v___x_213_, v___x_235_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v___x_236_);
v___x_238_ = v___x_198_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_size_195_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(lean_object* v_a_243_, lean_object* v_b_244_, lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_dec(v_b_244_);
lean_dec(v_a_243_);
return v_x_245_;
}
else
{
lean_object* v_key_246_; lean_object* v_value_247_; lean_object* v_tail_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_260_; 
v_key_246_ = lean_ctor_get(v_x_245_, 0);
v_value_247_ = lean_ctor_get(v_x_245_, 1);
v_tail_248_ = lean_ctor_get(v_x_245_, 2);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_245_);
if (v_isSharedCheck_260_ == 0)
{
v___x_250_ = v_x_245_;
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_tail_248_);
lean_inc(v_value_247_);
lean_inc(v_key_246_);
lean_dec(v_x_245_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
uint8_t v___x_252_; 
v___x_252_ = lean_level_eq(v_key_246_, v_a_243_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_243_, v_b_244_, v_tail_248_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 2, v___x_253_);
v___x_255_ = v___x_250_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_key_246_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_value_247_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
else
{
lean_object* v___x_258_; 
lean_dec(v_value_247_);
lean_dec(v_key_246_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v_b_244_);
lean_ctor_set(v___x_250_, 0, v_a_243_);
v___x_258_ = v___x_250_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_243_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_b_244_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_tail_248_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
return v_x_261_;
}
else
{
lean_object* v_key_263_; lean_object* v_value_264_; lean_object* v_tail_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_288_; 
v_key_263_ = lean_ctor_get(v_x_262_, 0);
v_value_264_ = lean_ctor_get(v_x_262_, 1);
v_tail_265_ = lean_ctor_get(v_x_262_, 2);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_288_ == 0)
{
v___x_267_ = v_x_262_;
v_isShared_268_ = v_isSharedCheck_288_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_tail_265_);
lean_inc(v_value_264_);
lean_inc(v_key_263_);
lean_dec(v_x_262_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_288_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v_fold_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_269_ = lean_array_get_size(v_x_261_);
v___x_270_ = l_Lean_Level_hash(v_key_263_);
v___x_271_ = 32ULL;
v___x_272_ = lean_uint64_shift_right(v___x_270_, v___x_271_);
v_fold_273_ = lean_uint64_xor(v___x_270_, v___x_272_);
v___x_274_ = 16ULL;
v___x_275_ = lean_uint64_shift_right(v_fold_273_, v___x_274_);
v___x_276_ = lean_uint64_xor(v_fold_273_, v___x_275_);
v___x_277_ = lean_uint64_to_usize(v___x_276_);
v___x_278_ = lean_usize_of_nat(v___x_269_);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_sub(v___x_278_, v___x_279_);
v___x_281_ = lean_usize_land(v___x_277_, v___x_280_);
v___x_282_ = lean_array_uget_borrowed(v_x_261_, v___x_281_);
lean_inc(v___x_282_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 2, v___x_282_);
v___x_284_ = v___x_267_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_key_263_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_value_264_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v___x_282_);
v___x_284_ = v_reuseFailAlloc_287_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; 
v___x_285_ = lean_array_uset(v_x_261_, v___x_281_, v___x_284_);
v_x_261_ = v___x_285_;
v_x_262_ = v_tail_265_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(lean_object* v_i_289_, lean_object* v_source_290_, lean_object* v_target_291_){
_start:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_array_get_size(v_source_290_);
v___x_293_ = lean_nat_dec_lt(v_i_289_, v___x_292_);
if (v___x_293_ == 0)
{
lean_dec_ref(v_source_290_);
lean_dec(v_i_289_);
return v_target_291_;
}
else
{
lean_object* v_es_294_; lean_object* v___x_295_; lean_object* v_source_296_; lean_object* v_target_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_es_294_ = lean_array_fget(v_source_290_, v_i_289_);
v___x_295_ = lean_box(0);
v_source_296_ = lean_array_fset(v_source_290_, v_i_289_, v___x_295_);
v_target_297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(v_target_291_, v_es_294_);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_i_289_, v___x_298_);
lean_dec(v_i_289_);
v_i_289_ = v___x_299_;
v_source_290_ = v_source_296_;
v_target_291_ = v_target_297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(lean_object* v_data_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_nbuckets_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_302_ = lean_array_get_size(v_data_301_);
v___x_303_ = lean_unsigned_to_nat(2u);
v_nbuckets_304_ = lean_nat_mul(v___x_302_, v___x_303_);
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_box(0);
v___x_307_ = lean_mk_array(v_nbuckets_304_, v___x_306_);
v___x_308_ = lean_array_propagate_mark(v_data_301_, v___x_307_);
v___x_309_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(v___x_305_, v_data_301_, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(lean_object* v_a_310_, lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 0;
return v___x_312_;
}
else
{
lean_object* v_key_313_; lean_object* v_tail_314_; uint8_t v___x_315_; 
v_key_313_ = lean_ctor_get(v_x_311_, 0);
v_tail_314_ = lean_ctor_get(v_x_311_, 2);
v___x_315_ = lean_level_eq(v_key_313_, v_a_310_);
if (v___x_315_ == 0)
{
v_x_311_ = v_tail_314_;
goto _start;
}
else
{
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg___boxed(lean_object* v_a_317_, lean_object* v_x_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_317_, v_x_318_);
lean_dec(v_x_318_);
lean_dec(v_a_317_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(lean_object* v_m_321_, lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
lean_object* v_size_324_; lean_object* v_buckets_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_368_; 
v_size_324_ = lean_ctor_get(v_m_321_, 0);
v_buckets_325_ = lean_ctor_get(v_m_321_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_m_321_);
if (v_isSharedCheck_368_ == 0)
{
v___x_327_ = v_m_321_;
v_isShared_328_ = v_isSharedCheck_368_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_buckets_325_);
lean_inc(v_size_324_);
lean_dec(v_m_321_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_368_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v_fold_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v_bkt_342_; uint8_t v___x_343_; 
v___x_329_ = lean_array_get_size(v_buckets_325_);
v___x_330_ = l_Lean_Level_hash(v_a_322_);
v___x_331_ = 32ULL;
v___x_332_ = lean_uint64_shift_right(v___x_330_, v___x_331_);
v_fold_333_ = lean_uint64_xor(v___x_330_, v___x_332_);
v___x_334_ = 16ULL;
v___x_335_ = lean_uint64_shift_right(v_fold_333_, v___x_334_);
v___x_336_ = lean_uint64_xor(v_fold_333_, v___x_335_);
v___x_337_ = lean_uint64_to_usize(v___x_336_);
v___x_338_ = lean_usize_of_nat(v___x_329_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_sub(v___x_338_, v___x_339_);
v___x_341_ = lean_usize_land(v___x_337_, v___x_340_);
v_bkt_342_ = lean_array_uget_borrowed(v_buckets_325_, v___x_341_);
v___x_343_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_322_, v_bkt_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v_size_x27_345_; lean_object* v___x_346_; lean_object* v_buckets_x27_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_344_ = lean_unsigned_to_nat(1u);
v_size_x27_345_ = lean_nat_add(v_size_324_, v___x_344_);
lean_dec(v_size_324_);
lean_inc(v_bkt_342_);
v___x_346_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_346_, 0, v_a_322_);
lean_ctor_set(v___x_346_, 1, v_b_323_);
lean_ctor_set(v___x_346_, 2, v_bkt_342_);
v_buckets_x27_347_ = lean_array_uset(v_buckets_325_, v___x_341_, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(4u);
v___x_349_ = lean_nat_mul(v_size_x27_345_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(3u);
v___x_351_ = lean_nat_div(v___x_349_, v___x_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_array_get_size(v_buckets_x27_347_);
v___x_353_ = lean_nat_dec_le(v___x_351_, v___x_352_);
lean_dec(v___x_351_);
if (v___x_353_ == 0)
{
lean_object* v_val_354_; lean_object* v___x_356_; 
v_val_354_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(v_buckets_x27_347_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_val_354_);
lean_ctor_set(v___x_327_, 0, v_size_x27_345_);
v___x_356_ = v___x_327_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_size_x27_345_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_val_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
else
{
lean_object* v___x_359_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_buckets_x27_347_);
lean_ctor_set(v___x_327_, 0, v_size_x27_345_);
v___x_359_ = v___x_327_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_size_x27_345_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_buckets_x27_347_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
lean_object* v___x_361_; lean_object* v_buckets_x27_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
lean_inc(v_bkt_342_);
v___x_361_ = lean_box(0);
v_buckets_x27_362_ = lean_array_uset(v_buckets_325_, v___x_341_, v___x_361_);
v___x_363_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_322_, v_b_323_, v_bkt_342_);
v___x_364_ = lean_array_uset(v_buckets_x27_362_, v___x_341_, v___x_363_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_364_);
v___x_366_ = v___x_327_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_size_324_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_unsigned_to_nat(524288u);
v___x_371_ = lean_mk_array(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__0, &l_LeanExport_M_run___redArg___closed__0_once, _init_l_LeanExport_M_run___redArg___closed__0);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_box(0);
v___x_377_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__1, &l_LeanExport_M_run___redArg___closed__1_once, _init_l_LeanExport_M_run___redArg___closed__1);
v___x_378_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v___x_377_, v___x_376_, v___x_375_);
return v___x_378_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_box(0);
v___x_380_ = lean_unsigned_to_nat(2048u);
v___x_381_ = lean_mk_array(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__4(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__3, &l_LeanExport_M_run___redArg___closed__3_once, _init_l_LeanExport_M_run___redArg___closed__3);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_box(0);
v___x_387_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__4, &l_LeanExport_M_run___redArg___closed__4_once, _init_l_LeanExport_M_run___redArg___closed__4);
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v___x_387_, v___x_386_, v___x_385_);
return v___x_388_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__6(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_box(0);
v___x_390_ = lean_unsigned_to_nat(16777216u);
v___x_391_ = lean_mk_array(v___x_390_, v___x_389_);
return v___x_391_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__6, &l_LeanExport_M_run___redArg___closed__6_once, _init_l_LeanExport_M_run___redArg___closed__6);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__8(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_box(0);
v___x_396_ = lean_unsigned_to_nat(16u);
v___x_397_ = lean_mk_array(v___x_396_, v___x_395_);
return v___x_397_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__9(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__8, &l_LeanExport_M_run___redArg___closed__8_once, _init_l_LeanExport_M_run___redArg___closed__8);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___x_398_);
return v___x_400_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__10(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = lean_box(0);
v___x_402_ = lean_unsigned_to_nat(262144u);
v___x_403_ = lean_mk_array(v___x_402_, v___x_401_);
return v___x_403_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__11(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__10, &l_LeanExport_M_run___redArg___closed__10_once, _init_l_LeanExport_M_run___redArg___closed__10);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
return v___x_406_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__12(void){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_407_ = lean_box(1);
v___x_408_ = 0;
v___x_409_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__11, &l_LeanExport_M_run___redArg___closed__11_once, _init_l_LeanExport_M_run___redArg___closed__11);
v___x_410_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__9, &l_LeanExport_M_run___redArg___closed__9_once, _init_l_LeanExport_M_run___redArg___closed__9);
v___x_411_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__7, &l_LeanExport_M_run___redArg___closed__7_once, _init_l_LeanExport_M_run___redArg___closed__7);
v___x_412_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__5, &l_LeanExport_M_run___redArg___closed__5_once, _init_l_LeanExport_M_run___redArg___closed__5);
v___x_413_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__2, &l_LeanExport_M_run___redArg___closed__2_once, _init_l_LeanExport_M_run___redArg___closed__2);
v___x_414_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_412_);
lean_ctor_set(v___x_414_, 2, v___x_411_);
lean_ctor_set(v___x_414_, 3, v___x_410_);
lean_ctor_set(v___x_414_, 4, v___x_409_);
lean_ctor_set(v___x_414_, 5, v___x_407_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*6, v___x_408_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*6 + 1, v___x_408_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*6 + 2, v___x_408_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg(lean_object* v_env_415_, lean_object* v_act_416_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__12, &l_LeanExport_M_run___redArg___closed__12_once, _init_l_LeanExport_M_run___redArg___closed__12);
v___x_419_ = lean_apply_3(v_act_416_, v_env_415_, v___x_418_, lean_box(0));
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_428_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_fst_424_; lean_object* v___x_426_; 
v_fst_424_ = lean_ctor_get(v_a_420_, 0);
lean_inc(v_fst_424_);
lean_dec(v_a_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v_fst_424_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_fst_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
v_a_429_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_419_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_419_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg___boxed(lean_object* v_env_437_, lean_object* v_act_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_LeanExport_M_run___redArg(v_env_437_, v_act_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run(lean_object* v_00_u03b1_441_, lean_object* v_env_442_, lean_object* v_act_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_LeanExport_M_run___redArg(v_env_442_, v_act_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___boxed(lean_object* v_00_u03b1_446_, lean_object* v_env_447_, lean_object* v_act_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_LeanExport_M_run(v_00_u03b1_446_, v_env_447_, v_act_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0(lean_object* v_00_u03b2_451_, lean_object* v_m_452_, lean_object* v_a_453_, lean_object* v_b_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v_m_452_, v_a_453_, v_b_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1(lean_object* v_00_u03b2_456_, lean_object* v_m_457_, lean_object* v_a_458_, lean_object* v_b_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v_m_457_, v_a_458_, v_b_459_);
return v___x_460_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(lean_object* v_00_u03b2_461_, lean_object* v_a_462_, lean_object* v_x_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_462_, v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___boxed(lean_object* v_00_u03b2_465_, lean_object* v_a_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(v_00_u03b2_465_, v_a_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec(v_a_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1(lean_object* v_00_u03b2_470_, lean_object* v_data_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(v_data_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2(lean_object* v_00_u03b2_473_, lean_object* v_a_474_, lean_object* v_b_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_474_, v_b_475_, v_x_476_);
return v___x_477_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(lean_object* v_00_u03b2_478_, lean_object* v_a_479_, lean_object* v_x_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_479_, v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___boxed(lean_object* v_00_u03b2_482_, lean_object* v_a_483_, lean_object* v_x_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(v_00_u03b2_482_, v_a_483_, v_x_484_);
lean_dec(v_x_484_);
lean_dec(v_a_483_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5(lean_object* v_00_u03b2_487_, lean_object* v_data_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(v_data_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6(lean_object* v_00_u03b2_490_, lean_object* v_a_491_, lean_object* v_b_492_, lean_object* v_x_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_491_, v_b_492_, v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_495_, lean_object* v_i_496_, lean_object* v_source_497_, lean_object* v_target_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(v_i_496_, v_source_497_, v_target_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7(lean_object* v_00_u03b2_500_, lean_object* v_i_501_, lean_object* v_source_502_, lean_object* v_target_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(v_i_501_, v_source_502_, v_target_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(v_x_506_, v_x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(v_x_510_, v_x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(lean_object* v_val_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v_toConstantVal_515_; lean_object* v_name_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_toConstantVal_515_ = lean_ctor_get(v_val_513_, 0);
lean_inc_ref(v_toConstantVal_515_);
lean_dec_ref(v_val_513_);
v_name_516_ = lean_ctor_get(v_toConstantVal_515_, 0);
lean_inc(v_name_516_);
lean_dec_ref(v_toConstantVal_515_);
v___x_517_ = l_Lean_NameSet_empty;
v___x_518_ = l_Lean_NameSet_insert(v___x_517_, v_name_516_);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
else
{
lean_object* v_toConstantVal_520_; lean_object* v_val_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_530_; 
v_toConstantVal_520_ = lean_ctor_get(v_val_513_, 0);
lean_inc_ref(v_toConstantVal_520_);
lean_dec_ref(v_val_513_);
v_val_521_ = lean_ctor_get(v_x_514_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_530_ == 0)
{
v___x_523_ = v_x_514_;
v_isShared_524_ = v_isSharedCheck_530_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_val_521_);
lean_dec(v_x_514_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_530_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_name_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v_name_525_ = lean_ctor_get(v_toConstantVal_520_, 0);
lean_inc(v_name_525_);
lean_dec_ref(v_toConstantVal_520_);
v___x_526_ = l_Lean_NameSet_insert(v_val_521_, v_name_525_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_526_);
v___x_528_ = v___x_523_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(lean_object* v_val_531_, lean_object* v_k_532_, lean_object* v_t_533_){
_start:
{
if (lean_obj_tag(v_t_533_) == 0)
{
lean_object* v_size_534_; lean_object* v_k_535_; lean_object* v_v_536_; lean_object* v_l_537_; lean_object* v_r_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_553_; 
v_size_534_ = lean_ctor_get(v_t_533_, 0);
v_k_535_ = lean_ctor_get(v_t_533_, 1);
v_v_536_ = lean_ctor_get(v_t_533_, 2);
v_l_537_ = lean_ctor_get(v_t_533_, 3);
v_r_538_ = lean_ctor_get(v_t_533_, 4);
v_isSharedCheck_553_ = !lean_is_exclusive(v_t_533_);
if (v_isSharedCheck_553_ == 0)
{
v___x_540_ = v_t_533_;
v_isShared_541_ = v_isSharedCheck_553_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_r_538_);
lean_inc(v_l_537_);
lean_inc(v_v_536_);
lean_inc(v_k_535_);
lean_inc(v_size_534_);
lean_dec(v_t_533_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_553_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
uint8_t v___x_542_; 
v___x_542_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_532_, v_k_535_);
switch(v___x_542_)
{
case 0:
{
lean_object* v_impl_543_; lean_object* v___x_544_; 
lean_del_object(v___x_540_);
lean_dec(v_size_534_);
v_impl_543_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_531_, v_k_532_, v_l_537_);
v___x_544_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_535_, v_v_536_, v_impl_543_, v_r_538_);
return v___x_544_;
}
case 1:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_val_547_; lean_object* v___x_549_; 
lean_dec(v_k_535_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_v_536_);
v___x_546_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(v_val_531_, v___x_545_);
v_val_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_547_);
lean_dec(v___x_546_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 2, v_val_547_);
lean_ctor_set(v___x_540_, 1, v_k_532_);
v___x_549_ = v___x_540_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_size_534_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_k_532_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_val_547_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_l_537_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_r_538_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
default: 
{
lean_object* v_impl_551_; lean_object* v___x_552_; 
lean_del_object(v___x_540_);
lean_dec(v_size_534_);
v_impl_551_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_531_, v_k_532_, v_r_538_);
v___x_552_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_535_, v_v_536_, v_l_537_, v_impl_551_);
return v___x_552_;
}
}
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_val_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_554_ = lean_box(0);
v___x_555_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(v_val_531_, v___x_554_);
v_val_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_val_556_);
lean_dec(v___x_555_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v_k_532_);
lean_ctor_set(v___x_558_, 2, v_val_556_);
lean_ctor_set(v___x_558_, 3, v_t_533_);
lean_ctor_set(v___x_558_, 4, v_t_533_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(lean_object* v_val_559_, lean_object* v_as_x27_560_, lean_object* v_b_561_, lean_object* v___y_562_){
_start:
{
if (lean_obj_tag(v_as_x27_560_) == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec_ref(v_val_559_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_b_561_);
lean_ctor_set(v___x_564_, 1, v___y_562_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
else
{
lean_object* v_head_566_; lean_object* v_tail_567_; lean_object* v___x_568_; 
v_head_566_ = lean_ctor_get(v_as_x27_560_, 0);
v_tail_567_ = lean_ctor_get(v_as_x27_560_, 1);
lean_inc(v_head_566_);
lean_inc_ref(v_val_559_);
v___x_568_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_559_, v_head_566_, v_b_561_);
v_as_x27_560_ = v_tail_567_;
v_b_561_ = v___x_568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg___boxed(lean_object* v_val_570_, lean_object* v_as_x27_571_, lean_object* v_b_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_570_, v_as_x27_571_, v_b_572_, v___y_573_);
lean_dec(v_as_x27_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0(lean_object* v_x_576_, lean_object* v_y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_a_583_; lean_object* v_snd_584_; 
if (lean_obj_tag(v_y_577_) == 7)
{
lean_object* v_val_590_; lean_object* v_all_591_; lean_object* v___x_592_; lean_object* v_a_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; 
v_val_590_ = lean_ctor_get(v_y_577_, 0);
lean_inc_ref(v_val_590_);
lean_dec_ref_known(v_y_577_, 1);
v_all_591_ = lean_ctor_get(v_val_590_, 1);
lean_inc(v_all_591_);
v___x_592_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_590_, v_all_591_, v___y_578_, v___y_580_);
lean_dec(v_all_591_);
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v___x_592_);
v_fst_594_ = lean_ctor_get(v_a_593_, 0);
lean_inc(v_fst_594_);
v_snd_595_ = lean_ctor_get(v_a_593_, 1);
lean_inc(v_snd_595_);
lean_dec(v_a_593_);
v_a_583_ = v_fst_594_;
v_snd_584_ = v_snd_595_;
goto v___jp_582_;
}
else
{
lean_dec_ref(v_y_577_);
v_a_583_ = v___y_578_;
v_snd_584_ = v___y_580_;
goto v___jp_582_;
}
v___jp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_585_ = lean_box(0);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_a_583_);
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_snd_584_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0___boxed(lean_object* v_x_596_, lean_object* v_y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_LeanExport_initState___lam__0(v_x_596_, v_y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v_x_596_);
return v_res_602_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__2(lean_object* v_x_604_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
uint8_t v___x_605_; 
v___x_605_ = 0;
return v___x_605_;
}
else
{
lean_object* v_head_606_; lean_object* v_tail_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_head_606_ = lean_ctor_get(v_x_604_, 0);
v_tail_607_ = lean_ctor_get(v_x_604_, 1);
v___x_608_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__2___closed__0));
v___x_609_ = lean_string_dec_eq(v_head_606_, v___x_608_);
if (v___x_609_ == 0)
{
v_x_604_ = v_tail_607_;
goto _start;
}
else
{
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__2___boxed(lean_object* v_x_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l_List_any___at___00LeanExport_initState_spec__2(v_x_611_);
lean_dec(v_x_611_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__0(lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
else
{
lean_object* v_head_617_; lean_object* v_tail_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_head_617_ = lean_ctor_get(v_x_615_, 0);
v_tail_618_ = lean_ctor_get(v_x_615_, 1);
v___x_619_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__0___closed__0));
v___x_620_ = lean_string_dec_eq(v_head_617_, v___x_619_);
if (v___x_620_ == 0)
{
v_x_615_ = v_tail_618_;
goto _start;
}
else
{
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__0___boxed(lean_object* v_x_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_List_any___at___00LeanExport_initState_spec__0(v_x_622_);
lean_dec(v_x_622_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(lean_object* v_f_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v_f_625_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v_x_626_);
lean_ctor_set(v___x_632_, 1, v___y_628_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___y_630_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
else
{
lean_object* v_key_636_; lean_object* v_value_637_; lean_object* v_tail_638_; lean_object* v___x_639_; 
v_key_636_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_key_636_);
v_value_637_ = lean_ctor_get(v_x_627_, 1);
lean_inc(v_value_637_);
v_tail_638_ = lean_ctor_get(v_x_627_, 2);
lean_inc(v_tail_638_);
lean_dec_ref_known(v_x_627_, 3);
lean_inc_ref(v_f_625_);
lean_inc_ref(v___y_629_);
v___x_639_ = lean_apply_6(v_f_625_, v_key_636_, v_value_637_, v___y_628_, v___y_629_, v___y_630_, lean_box(0));
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v_fst_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
v_fst_641_ = lean_ctor_get(v_a_640_, 0);
if (lean_obj_tag(v_fst_641_) == 0)
{
lean_dec(v_a_640_);
lean_dec(v_tail_638_);
lean_dec_ref(v_f_625_);
return v___x_639_;
}
else
{
lean_object* v_a_642_; lean_object* v_snd_643_; lean_object* v_fst_644_; lean_object* v_snd_645_; 
lean_dec_ref_known(v___x_639_, 1);
v_a_642_ = lean_ctor_get(v_fst_641_, 0);
lean_inc(v_a_642_);
v_snd_643_ = lean_ctor_get(v_a_640_, 1);
lean_inc(v_snd_643_);
lean_dec(v_a_640_);
v_fst_644_ = lean_ctor_get(v_a_642_, 0);
lean_inc(v_fst_644_);
v_snd_645_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_snd_645_);
lean_dec(v_a_642_);
v_x_626_ = v_fst_644_;
v_x_627_ = v_tail_638_;
v___y_628_ = v_snd_645_;
v___y_630_ = v_snd_643_;
goto _start;
}
}
else
{
lean_dec(v_tail_638_);
lean_dec_ref(v_f_625_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___boxed(lean_object* v_f_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_647_, v_x_648_, v_x_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(lean_object* v_f_655_, lean_object* v_as_656_, size_t v_i_657_, size_t v_stop_658_, lean_object* v_b_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_eq(v_i_657_, v_stop_658_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_array_uget_borrowed(v_as_656_, v_i_657_);
v___x_666_ = lean_box(0);
lean_inc(v___x_665_);
lean_inc_ref(v_f_655_);
v___x_667_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_655_, v___x_666_, v___x_665_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v_fst_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_fst_669_ = lean_ctor_get(v_a_668_, 0);
if (lean_obj_tag(v_fst_669_) == 0)
{
lean_dec_ref(v_f_655_);
return v___x_667_;
}
else
{
lean_object* v_a_670_; lean_object* v_snd_671_; lean_object* v_fst_672_; lean_object* v_snd_673_; size_t v___x_674_; size_t v___x_675_; 
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v_a_670_ = lean_ctor_get(v_fst_669_, 0);
lean_inc(v_a_670_);
v_snd_671_ = lean_ctor_get(v_a_668_, 1);
lean_inc(v_snd_671_);
lean_dec(v_a_668_);
v_fst_672_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_fst_672_);
v_snd_673_ = lean_ctor_get(v_a_670_, 1);
lean_inc(v_snd_673_);
lean_dec(v_a_670_);
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_add(v_i_657_, v___x_674_);
v_i_657_ = v___x_675_;
v_b_659_ = v_fst_672_;
v___y_660_ = v_snd_673_;
v___y_662_ = v_snd_671_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_655_);
return v___x_667_;
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec_ref(v_f_655_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_b_659_);
lean_ctor_set(v___x_677_, 1, v___y_660_);
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___y_662_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg___boxed(lean_object* v_f_681_, lean_object* v_as_682_, lean_object* v_i_683_, lean_object* v_stop_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
size_t v_i_boxed_690_; size_t v_stop_boxed_691_; lean_object* v_res_692_; 
v_i_boxed_690_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_stop_boxed_691_ = lean_unbox_usize(v_stop_684_);
lean_dec(v_stop_684_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_681_, v_as_682_, v_i_boxed_690_, v_stop_boxed_691_, v_b_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v_as_682_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(lean_object* v_f_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
lean_inc_ref(v___y_698_);
v___x_701_ = lean_apply_6(v_f_693_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, lean_box(0));
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_f_702_, lean_object* v_x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(v_f_702_, v_x_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(lean_object* v_f_711_, lean_object* v_keys_712_, lean_object* v_vals_713_, lean_object* v_i_714_, lean_object* v_acc_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = lean_array_get_size(v_keys_712_);
v___x_721_ = lean_nat_dec_lt(v_i_714_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec(v_i_714_);
lean_dec_ref(v_f_711_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_acc_715_);
lean_ctor_set(v___x_722_, 1, v___y_716_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___y_718_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v_k_726_; lean_object* v_v_727_; lean_object* v___x_728_; 
v_k_726_ = lean_array_fget_borrowed(v_keys_712_, v_i_714_);
v_v_727_ = lean_array_fget_borrowed(v_vals_713_, v_i_714_);
lean_inc_ref(v_f_711_);
lean_inc_ref(v___y_717_);
lean_inc(v_v_727_);
lean_inc(v_k_726_);
v___x_728_ = lean_apply_7(v_f_711_, v_acc_715_, v_k_726_, v_v_727_, v___y_716_, v___y_717_, v___y_718_, lean_box(0));
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v_fst_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
v_fst_730_ = lean_ctor_get(v_a_729_, 0);
if (lean_obj_tag(v_fst_730_) == 0)
{
lean_dec(v_a_729_);
lean_dec(v_i_714_);
lean_dec_ref(v_f_711_);
return v___x_728_;
}
else
{
lean_object* v_a_731_; lean_object* v_snd_732_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec_ref_known(v___x_728_, 1);
v_a_731_ = lean_ctor_get(v_fst_730_, 0);
lean_inc(v_a_731_);
v_snd_732_ = lean_ctor_get(v_a_729_, 1);
lean_inc(v_snd_732_);
lean_dec(v_a_729_);
v_fst_733_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_fst_733_);
v_snd_734_ = lean_ctor_get(v_a_731_, 1);
lean_inc(v_snd_734_);
lean_dec(v_a_731_);
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_add(v_i_714_, v___x_735_);
lean_dec(v_i_714_);
v_i_714_ = v___x_736_;
v_acc_715_ = v_fst_733_;
v___y_716_ = v_snd_734_;
v___y_718_ = v_snd_732_;
goto _start;
}
}
else
{
lean_dec(v_i_714_);
lean_dec_ref(v_f_711_);
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_f_738_, lean_object* v_keys_739_, lean_object* v_vals_740_, lean_object* v_i_741_, lean_object* v_acc_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_738_, v_keys_739_, v_vals_740_, v_i_741_, v_acc_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v_vals_740_);
lean_dec_ref(v_keys_739_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_f_748_, lean_object* v_as_749_, size_t v_i_750_, size_t v_stop_751_, lean_object* v_b_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_fst_758_; lean_object* v_snd_759_; lean_object* v_snd_760_; lean_object* v___y_765_; uint8_t v___x_772_; 
v___x_772_ = lean_usize_dec_eq(v_i_750_, v_stop_751_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
v___x_773_ = lean_array_uget_borrowed(v_as_749_, v_i_750_);
switch(lean_obj_tag(v___x_773_))
{
case 0:
{
lean_object* v_key_774_; lean_object* v_val_775_; lean_object* v___x_776_; 
v_key_774_ = lean_ctor_get(v___x_773_, 0);
v_val_775_ = lean_ctor_get(v___x_773_, 1);
lean_inc_ref(v_f_748_);
lean_inc_ref(v___y_754_);
lean_inc(v_val_775_);
lean_inc(v_key_774_);
v___x_776_ = lean_apply_7(v_f_748_, v_b_752_, v_key_774_, v_val_775_, v___y_753_, v___y_754_, v___y_755_, lean_box(0));
v___y_765_ = v___x_776_;
goto v___jp_764_;
}
case 1:
{
lean_object* v_node_777_; lean_object* v___x_778_; 
v_node_777_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_node_777_);
lean_inc_ref(v_f_748_);
v___x_778_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_748_, v_node_777_, v_b_752_, v___y_753_, v___y_754_, v___y_755_);
v___y_765_ = v___x_778_;
goto v___jp_764_;
}
default: 
{
v_fst_758_ = v_b_752_;
v_snd_759_ = v___y_753_;
v_snd_760_ = v___y_755_;
goto v___jp_757_;
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref(v_f_748_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_b_752_);
lean_ctor_set(v___x_779_, 1, v___y_753_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___y_755_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
v___jp_757_:
{
size_t v___x_761_; size_t v___x_762_; 
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_750_, v___x_761_);
v_i_750_ = v___x_762_;
v_b_752_ = v_fst_758_;
v___y_753_ = v_snd_759_;
v___y_755_ = v_snd_760_;
goto _start;
}
v___jp_764_:
{
if (lean_obj_tag(v___y_765_) == 0)
{
lean_object* v_a_766_; lean_object* v_fst_767_; 
v_a_766_ = lean_ctor_get(v___y_765_, 0);
v_fst_767_ = lean_ctor_get(v_a_766_, 0);
if (lean_obj_tag(v_fst_767_) == 0)
{
lean_dec_ref(v_f_748_);
return v___y_765_;
}
else
{
lean_object* v_a_768_; lean_object* v_snd_769_; lean_object* v_fst_770_; lean_object* v_snd_771_; 
lean_inc(v_a_766_);
lean_dec_ref_known(v___y_765_, 1);
v_a_768_ = lean_ctor_get(v_fst_767_, 0);
lean_inc(v_a_768_);
v_snd_769_ = lean_ctor_get(v_a_766_, 1);
lean_inc(v_snd_769_);
lean_dec(v_a_766_);
v_fst_770_ = lean_ctor_get(v_a_768_, 0);
lean_inc(v_fst_770_);
v_snd_771_ = lean_ctor_get(v_a_768_, 1);
lean_inc(v_snd_771_);
lean_dec(v_a_768_);
v_fst_758_ = v_fst_770_;
v_snd_759_ = v_snd_771_;
v_snd_760_ = v_snd_769_;
goto v___jp_757_;
}
}
else
{
lean_dec_ref(v_f_748_);
return v___y_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_f_783_, lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v_es_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_806_; 
v_es_790_ = lean_ctor_get(v_x_784_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_806_ == 0)
{
v___x_792_ = v_x_784_;
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_es_790_);
lean_dec(v_x_784_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_array_get_size(v_es_790_);
v___x_796_ = lean_nat_dec_lt(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_dec_ref(v_es_790_);
lean_dec_ref(v_f_783_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_x_785_);
lean_ctor_set(v___x_797_, 1, v___y_786_);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 1);
lean_ctor_set(v___x_792_, 0, v___x_797_);
v___x_799_ = v___x_792_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_802_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___y_788_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
else
{
size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
lean_del_object(v___x_792_);
v___x_803_ = ((size_t)0ULL);
v___x_804_ = lean_usize_of_nat(v___x_795_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_783_, v_es_790_, v___x_803_, v___x_804_, v_x_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec_ref(v_es_790_);
return v___x_805_;
}
}
}
else
{
lean_object* v_ks_807_; lean_object* v_vs_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_ks_807_ = lean_ctor_get(v_x_784_, 0);
lean_inc_ref(v_ks_807_);
v_vs_808_ = lean_ctor_get(v_x_784_, 1);
lean_inc_ref(v_vs_808_);
lean_dec_ref_known(v_x_784_, 2);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_783_, v_ks_807_, v_vs_808_, v___x_809_, v_x_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec_ref(v_vs_808_);
lean_dec_ref(v_ks_807_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_f_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_811_, v_x_812_, v_x_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_f_819_, lean_object* v_as_820_, lean_object* v_i_821_, lean_object* v_stop_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
size_t v_i_boxed_828_; size_t v_stop_boxed_829_; lean_object* v_res_830_; 
v_i_boxed_828_ = lean_unbox_usize(v_i_821_);
lean_dec(v_i_821_);
v_stop_boxed_829_ = lean_unbox_usize(v_stop_822_);
lean_dec(v_stop_822_);
v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_819_, v_as_820_, v_i_boxed_828_, v_stop_boxed_829_, v_b_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec_ref(v_as_820_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(lean_object* v_map_831_, lean_object* v_f_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___f_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___f_837_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_837_, 0, v_f_832_);
v___x_838_ = lean_box(0);
v___x_839_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v___f_837_, v_map_831_, v___x_838_, v___y_833_, v___y_834_, v___y_835_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___boxed(lean_object* v_map_840_, lean_object* v_f_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_840_, v_f_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec_ref(v___y_843_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(lean_object* v_s_847_, lean_object* v_f_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_map_u2081_853_; lean_object* v_map_u2082_854_; lean_object* v_buckets_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_map_u2081_853_ = lean_ctor_get(v_s_847_, 0);
lean_inc_ref(v_map_u2081_853_);
v_map_u2082_854_ = lean_ctor_get(v_s_847_, 1);
lean_inc_ref(v_map_u2082_854_);
lean_dec_ref(v_s_847_);
v_buckets_855_ = lean_ctor_get(v_map_u2081_853_, 1);
lean_inc_ref(v_buckets_855_);
lean_dec_ref(v_map_u2081_853_);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_array_get_size(v_buckets_855_);
v___x_858_ = lean_nat_dec_lt(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
lean_dec_ref(v_buckets_855_);
v___x_859_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_854_, v_f_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_859_;
}
else
{
lean_object* v___x_860_; size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; 
v___x_860_ = lean_box(0);
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_857_);
lean_inc_ref(v_f_848_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_848_, v_buckets_855_, v___x_861_, v___x_862_, v___x_860_, v___y_849_, v___y_850_, v___y_851_);
lean_dec_ref(v_buckets_855_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v_fst_865_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_fst_865_ = lean_ctor_get(v_a_864_, 0);
if (lean_obj_tag(v_fst_865_) == 0)
{
lean_dec_ref(v_map_u2082_854_);
lean_dec_ref(v_f_848_);
return v___x_863_;
}
else
{
lean_object* v_a_866_; lean_object* v_snd_867_; lean_object* v_snd_868_; lean_object* v___x_869_; 
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v_a_866_ = lean_ctor_get(v_fst_865_, 0);
lean_inc(v_a_866_);
v_snd_867_ = lean_ctor_get(v_a_864_, 1);
lean_inc(v_snd_867_);
lean_dec(v_a_864_);
v_snd_868_ = lean_ctor_get(v_a_866_, 1);
lean_inc(v_snd_868_);
lean_dec(v_a_866_);
v___x_869_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_854_, v_f_848_, v_snd_868_, v___y_850_, v_snd_867_);
return v___x_869_;
}
}
else
{
lean_dec_ref(v_map_u2082_854_);
lean_dec_ref(v_f_848_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg___boxed(lean_object* v_s_870_, lean_object* v_f_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_870_, v_f_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_876_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
uint8_t v___x_879_; 
v___x_879_ = 0;
return v___x_879_;
}
else
{
lean_object* v_head_880_; lean_object* v_tail_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v_head_880_ = lean_ctor_get(v_x_878_, 0);
v_tail_881_ = lean_ctor_get(v_x_878_, 1);
v___x_882_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__1___closed__0));
v___x_883_ = lean_string_dec_eq(v_head_880_, v___x_882_);
if (v___x_883_ == 0)
{
v_x_878_ = v_tail_881_;
goto _start;
}
else
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object* v_x_885_){
_start:
{
uint8_t v_res_886_; lean_object* v_r_887_; 
v_res_886_ = l_List_any___at___00LeanExport_initState_spec__1(v_x_885_);
lean_dec(v_x_885_);
v_r_887_ = lean_box(v_res_886_);
return v_r_887_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState(lean_object* v_env_889_, lean_object* v_cliOptions_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___f_916_; lean_object* v_recursorMap_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___f_916_ = ((lean_object*)(l_LeanExport_initState___closed__0));
v_recursorMap_917_ = lean_box(1);
v___x_918_ = l_Lean_Environment_constants(v_env_889_);
v___x_919_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v___x_918_, v___f_916_, v_recursorMap_917_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v_fst_921_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
v_fst_921_ = lean_ctor_get(v_a_920_, 0);
if (lean_obj_tag(v_fst_921_) == 0)
{
lean_object* v_snd_922_; lean_object* v_a_923_; 
lean_inc_ref(v_fst_921_);
v_snd_922_ = lean_ctor_get(v_a_920_, 1);
lean_inc(v_snd_922_);
lean_dec(v_a_920_);
v_a_923_ = lean_ctor_get(v_fst_921_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v_fst_921_, 1);
v_fst_895_ = v_a_923_;
v_snd_896_ = v_snd_922_;
goto v___jp_894_;
}
else
{
lean_object* v_a_924_; lean_object* v_snd_925_; lean_object* v_snd_926_; 
v_a_924_ = lean_ctor_get(v_fst_921_, 0);
lean_inc(v_a_924_);
v_snd_925_ = lean_ctor_get(v_a_920_, 1);
lean_inc(v_snd_925_);
lean_dec(v_a_920_);
v_snd_926_ = lean_ctor_get(v_a_924_, 1);
lean_inc(v_snd_926_);
lean_dec(v_a_924_);
v_fst_895_ = v_snd_926_;
v_snd_896_ = v_snd_925_;
goto v___jp_894_;
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
v_a_927_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_919_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_919_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
v___jp_894_:
{
lean_object* v_visitedNames_897_; lean_object* v_visitedLevels_898_; lean_object* v_visitedExprs_899_; lean_object* v_visitedConstants_900_; lean_object* v_noMDataExprs_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_914_; 
v_visitedNames_897_ = lean_ctor_get(v_snd_896_, 0);
v_visitedLevels_898_ = lean_ctor_get(v_snd_896_, 1);
v_visitedExprs_899_ = lean_ctor_get(v_snd_896_, 2);
v_visitedConstants_900_ = lean_ctor_get(v_snd_896_, 3);
v_noMDataExprs_901_ = lean_ctor_get(v_snd_896_, 4);
v_isSharedCheck_914_ = !lean_is_exclusive(v_snd_896_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v_snd_896_, 5);
lean_dec(v_unused_915_);
v___x_903_ = v_snd_896_;
v_isShared_904_ = v_isSharedCheck_914_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_noMDataExprs_901_);
lean_inc(v_visitedConstants_900_);
lean_inc(v_visitedExprs_899_);
lean_inc(v_visitedLevels_898_);
lean_inc(v_visitedNames_897_);
lean_dec(v_snd_896_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_914_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; uint8_t v___x_906_; uint8_t v___x_907_; uint8_t v___x_908_; lean_object* v___x_910_; 
v___x_905_ = lean_box(0);
v___x_906_ = l_List_any___at___00LeanExport_initState_spec__0(v_cliOptions_890_);
v___x_907_ = l_List_any___at___00LeanExport_initState_spec__1(v_cliOptions_890_);
v___x_908_ = l_List_any___at___00LeanExport_initState_spec__2(v_cliOptions_890_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 5, v_fst_895_);
v___x_910_ = v___x_903_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_visitedNames_897_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_visitedLevels_898_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_visitedExprs_899_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_visitedConstants_900_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_noMDataExprs_901_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v_fst_895_);
v___x_910_ = v_reuseFailAlloc_913_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*6, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*6 + 1, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*6 + 2, v___x_908_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_905_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___boxed(lean_object* v_env_935_, lean_object* v_cliOptions_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_LeanExport_initState(v_env_935_, v_cliOptions_936_, v_a_937_, v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_cliOptions_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3(lean_object* v_val_941_, lean_object* v_k_942_, lean_object* v_t_943_, lean_object* v_hl_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_941_, v_k_942_, v_t_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(lean_object* v_val_946_, lean_object* v_as_947_, lean_object* v_as_x27_948_, lean_object* v_b_949_, lean_object* v_a_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_946_, v_as_x27_948_, v_b_949_, v___y_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___boxed(lean_object* v_val_955_, lean_object* v_as_956_, lean_object* v_as_x27_957_, lean_object* v_b_958_, lean_object* v_a_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(v_val_955_, v_as_956_, v_as_x27_957_, v_b_958_, v_a_959_, v___y_960_, v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v_as_x27_957_);
lean_dec(v_as_956_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(lean_object* v_00_u03b2_964_, lean_object* v_s_965_, lean_object* v_f_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_965_, v_f_966_, v___y_967_, v___y_968_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___boxed(lean_object* v_00_u03b2_972_, lean_object* v_s_973_, lean_object* v_f_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(v_00_u03b2_972_, v_s_973_, v_f_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_object* v_00_u03b2_980_, lean_object* v_f_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_981_, v_x_982_, v_x_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___boxed(lean_object* v_00_u03b2_989_, lean_object* v_f_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(v_00_u03b2_989_, v_f_990_, v_x_991_, v_x_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_object* v_00_u03b2_998_, lean_object* v_map_999_, lean_object* v_f_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_999_, v_f_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1006_, lean_object* v_map_1007_, lean_object* v_f_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(v_00_u03b2_1006_, v_map_1007_, v_f_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(lean_object* v_00_u03b2_1014_, lean_object* v_f_1015_, lean_object* v_as_1016_, size_t v_i_1017_, size_t v_stop_1018_, lean_object* v_b_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_1015_, v_as_1016_, v_i_1017_, v_stop_1018_, v_b_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1025_, lean_object* v_f_1026_, lean_object* v_as_1027_, lean_object* v_i_1028_, lean_object* v_stop_1029_, lean_object* v_b_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
size_t v_i_boxed_1035_; size_t v_stop_boxed_1036_; lean_object* v_res_1037_; 
v_i_boxed_1035_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_stop_boxed_1036_ = lean_unbox_usize(v_stop_1029_);
lean_dec(v_stop_1029_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(v_00_u03b2_1025_, v_f_1026_, v_as_1027_, v_i_boxed_1035_, v_stop_boxed_1036_, v_b_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_as_1027_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(lean_object* v_map_1038_, lean_object* v_f_1039_, lean_object* v_init_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1039_, v_map_1038_, v_init_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_map_1046_, lean_object* v_f_1047_, lean_object* v_init_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(v_map_1046_, v_f_1047_, v_init_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(lean_object* v_00_u03c3_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_map_1056_, lean_object* v_f_1057_, lean_object* v_init_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1057_, v_map_1056_, v_init_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03c3_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_map_1066_, lean_object* v_f_1067_, lean_object* v_init_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(v_00_u03c3_1064_, v_00_u03b2_1065_, v_map_1066_, v_f_1067_, v_init_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03c3_1074_, lean_object* v_00_u03b1_1075_, lean_object* v_00_u03b2_1076_, lean_object* v_f_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1077_, v_x_1078_, v_x_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03c3_1085_, lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_f_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(v_00_u03c3_1085_, v_00_u03b1_1086_, v_00_u03b2_1087_, v_f_1088_, v_x_1089_, v_x_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_00_u03c3_1098_, lean_object* v_f_1099_, lean_object* v_as_1100_, size_t v_i_1101_, size_t v_stop_1102_, lean_object* v_b_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_1099_, v_as_1100_, v_i_1101_, v_stop_1102_, v_b_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_00_u03c3_1111_, lean_object* v_f_1112_, lean_object* v_as_1113_, lean_object* v_i_1114_, lean_object* v_stop_1115_, lean_object* v_b_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
size_t v_i_boxed_1121_; size_t v_stop_boxed_1122_; lean_object* v_res_1123_; 
v_i_boxed_1121_ = lean_unbox_usize(v_i_1114_);
lean_dec(v_i_1114_);
v_stop_boxed_1122_ = lean_unbox_usize(v_stop_1115_);
lean_dec(v_stop_1115_);
v_res_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_1109_, v_00_u03b2_1110_, v_00_u03c3_1111_, v_f_1112_, v_as_1113_, v_i_boxed_1121_, v_stop_boxed_1122_, v_b_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec_ref(v_as_1113_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(lean_object* v_00_u03c3_1124_, lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_f_1127_, lean_object* v_keys_1128_, lean_object* v_vals_1129_, lean_object* v_heq_1130_, lean_object* v_i_1131_, lean_object* v_acc_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_1127_, v_keys_1128_, v_vals_1129_, v_i_1131_, v_acc_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03c3_1138_, lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_f_1141_, lean_object* v_keys_1142_, lean_object* v_vals_1143_, lean_object* v_heq_1144_, lean_object* v_i_1145_, lean_object* v_acc_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(v_00_u03c3_1138_, v_00_u03b1_1139_, v_00_u03b2_1140_, v_f_1141_, v_keys_1142_, v_vals_1143_, v_heq_1144_, v_i_1145_, v_acc_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec_ref(v_vals_1143_);
lean_dec_ref(v_keys_1142_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_x_1155_, lean_object* v_namespaced_1156_, lean_object* v_getM_1157_, lean_object* v_setM_1158_, lean_object* v_rec_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_inc_ref(v_getM_1157_);
lean_inc_ref(v_a_1161_);
v___x_1163_ = lean_apply_1(v_getM_1157_, v_a_1161_);
lean_inc(v_x_1155_);
lean_inc_ref(v_inst_1153_);
lean_inc_ref(v_inst_1154_);
v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1154_, v_inst_1153_, v___x_1163_, v_x_1155_);
lean_dec_ref(v___x_1163_);
if (lean_obj_tag(v___x_1164_) == 1)
{
lean_object* v_val_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v_rec_1159_);
lean_dec_ref(v_setM_1158_);
lean_dec_ref(v_getM_1157_);
lean_dec_ref(v_namespaced_1156_);
lean_dec(v_x_1155_);
lean_dec_ref(v_inst_1154_);
lean_dec_ref(v_inst_1153_);
v_val_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_val_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_val_1165_);
lean_ctor_set(v___x_1169_, 1, v_a_1161_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1169_);
v___x_1171_ = v___x_1167_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
else
{
lean_object* v___f_1174_; lean_object* v___x_1175_; 
lean_dec(v___x_1164_);
v___f_1174_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
lean_inc_ref(v_a_1160_);
v___x_1175_ = lean_apply_3(v_rec_1159_, v_a_1160_, v_a_1161_, lean_box(0));
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1210_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v_fst_1177_ = lean_ctor_get(v_a_1176_, 0);
v_snd_1178_ = lean_ctor_get(v_a_1176_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_a_1176_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1180_ = v_a_1176_;
v_isShared_1181_ = v_isSharedCheck_1210_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1178_);
lean_inc(v_fst_1177_);
lean_dec(v_a_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1210_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v_size_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_inc(v_snd_1178_);
v___x_1182_ = lean_apply_1(v_getM_1157_, v_snd_1178_);
v_size_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_n(v_size_1183_, 2);
v___x_1184_ = l_Lean_JsonNumber_fromNat(v_size_1183_);
v___x_1185_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
v___x_1186_ = l_Lean_Json_setObjVal_x21(v_fst_1177_, v_namespaced_1156_, v___x_1185_);
v___x_1187_ = l_Lean_Json_compress(v___x_1186_);
v___x_1188_ = l_IO_println___redArg(v___f_1174_, v___x_1187_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1200_; 
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v___x_1188_, 0);
lean_dec(v_unused_1201_);
v___x_1190_ = v___x_1188_;
v_isShared_1191_ = v_isSharedCheck_1200_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v___x_1188_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1200_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
lean_inc(v_size_1183_);
v___x_1192_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1154_, v_inst_1153_, v___x_1182_, v_x_1155_, v_size_1183_);
v___x_1193_ = lean_apply_2(v_setM_1158_, v_snd_1178_, v___x_1192_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1193_);
lean_ctor_set(v___x_1180_, 0, v_size_1183_);
v___x_1195_ = v___x_1180_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_size_1183_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1195_);
v___x_1197_ = v___x_1190_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_size_1183_);
lean_dec_ref(v___x_1182_);
lean_del_object(v___x_1180_);
lean_dec(v_snd_1178_);
lean_dec_ref(v_setM_1158_);
lean_dec(v_x_1155_);
lean_dec_ref(v_inst_1154_);
lean_dec_ref(v_inst_1153_);
v_a_1202_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1188_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1188_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
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
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_setM_1158_);
lean_dec_ref(v_getM_1157_);
lean_dec_ref(v_namespaced_1156_);
lean_dec(v_x_1155_);
lean_dec_ref(v_inst_1154_);
lean_dec_ref(v_inst_1153_);
v_a_1211_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1175_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1175_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
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
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___boxed(lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_x_1221_, lean_object* v_namespaced_1222_, lean_object* v_getM_1223_, lean_object* v_setM_1224_, lean_object* v_rec_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(v_inst_1219_, v_inst_1220_, v_x_1221_, v_namespaced_1222_, v_getM_1223_, v_setM_1224_, v_rec_1225_, v_a_1226_, v_a_1227_);
lean_dec_ref(v_a_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx(lean_object* v_00_u03b1_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_x_1233_, lean_object* v_namespaced_1234_, lean_object* v_getM_1235_, lean_object* v_setM_1236_, lean_object* v_rec_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_inc_ref(v_getM_1235_);
lean_inc_ref(v_a_1239_);
v___x_1241_ = lean_apply_1(v_getM_1235_, v_a_1239_);
lean_inc(v_x_1233_);
lean_inc_ref(v_inst_1231_);
lean_inc_ref(v_inst_1232_);
v___x_1242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1232_, v_inst_1231_, v___x_1241_, v_x_1233_);
lean_dec_ref(v___x_1241_);
if (lean_obj_tag(v___x_1242_) == 1)
{
lean_object* v_val_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_rec_1237_);
lean_dec_ref(v_setM_1236_);
lean_dec_ref(v_getM_1235_);
lean_dec_ref(v_namespaced_1234_);
lean_dec(v_x_1233_);
lean_dec_ref(v_inst_1232_);
lean_dec_ref(v_inst_1231_);
v_val_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_val_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_val_1243_);
lean_ctor_set(v___x_1247_, 1, v_a_1239_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
lean_object* v___f_1252_; lean_object* v___x_1253_; 
lean_dec(v___x_1242_);
v___f_1252_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
lean_inc_ref(v_a_1238_);
v___x_1253_ = lean_apply_3(v_rec_1237_, v_a_1238_, v_a_1239_, lean_box(0));
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v_fst_1255_; lean_object* v_snd_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1288_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v_fst_1255_ = lean_ctor_get(v_a_1254_, 0);
v_snd_1256_ = lean_ctor_get(v_a_1254_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_a_1254_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1258_ = v_a_1254_;
v_isShared_1259_ = v_isSharedCheck_1288_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_snd_1256_);
lean_inc(v_fst_1255_);
lean_dec(v_a_1254_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1288_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v_size_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_inc(v_snd_1256_);
v___x_1260_ = lean_apply_1(v_getM_1235_, v_snd_1256_);
v_size_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_n(v_size_1261_, 2);
v___x_1262_ = l_Lean_JsonNumber_fromNat(v_size_1261_);
v___x_1263_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
v___x_1264_ = l_Lean_Json_setObjVal_x21(v_fst_1255_, v_namespaced_1234_, v___x_1263_);
v___x_1265_ = l_Lean_Json_compress(v___x_1264_);
v___x_1266_ = l_IO_println___redArg(v___f_1252_, v___x_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1278_; 
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1266_, 0);
lean_dec(v_unused_1279_);
v___x_1268_ = v___x_1266_;
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v___x_1266_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
lean_inc(v_size_1261_);
v___x_1270_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1232_, v_inst_1231_, v___x_1260_, v_x_1233_, v_size_1261_);
v___x_1271_ = lean_apply_2(v_setM_1236_, v_snd_1256_, v___x_1270_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1271_);
lean_ctor_set(v___x_1258_, 0, v_size_1261_);
v___x_1273_ = v___x_1258_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_size_1261_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1273_);
v___x_1275_ = v___x_1268_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_size_1261_);
lean_dec_ref(v___x_1260_);
lean_del_object(v___x_1258_);
lean_dec(v_snd_1256_);
lean_dec_ref(v_setM_1236_);
lean_dec(v_x_1233_);
lean_dec_ref(v_inst_1232_);
lean_dec_ref(v_inst_1231_);
v_a_1280_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1266_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1266_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_setM_1236_);
lean_dec_ref(v_getM_1235_);
lean_dec_ref(v_namespaced_1234_);
lean_dec(v_x_1233_);
lean_dec_ref(v_inst_1232_);
lean_dec_ref(v_inst_1231_);
v_a_1289_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1253_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1253_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_x_1300_, lean_object* v_namespaced_1301_, lean_object* v_getM_1302_, lean_object* v_setM_1303_, lean_object* v_rec_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_LeanExport_Basic_0__LeanExport_getIdx(v_00_u03b1_1297_, v_inst_1298_, v_inst_1299_, v_x_1300_, v_namespaced_1301_, v_getM_1302_, v_setM_1303_, v_rec_1304_, v_a_1305_, v_a_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1308_;
}
}
static lean_object* _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_instMonadEIO___redArg();
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v___f_1315_; lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___f_1327_; lean_object* v___x_1423__overap_1328_; lean_object* v___x_1329_; 
v___x_1314_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_1315_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1315_, 0, v___x_1314_);
v___f_1316_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1316_, 0, v___x_1314_);
v___f_1317_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1317_, 0, v___x_1314_);
v___f_1318_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1318_, 0, v___x_1314_);
v___x_1319_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1319_, 0, lean_box(0));
lean_closure_set(v___x_1319_, 1, lean_box(0));
lean_closure_set(v___x_1319_, 2, v___x_1314_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___f_1315_);
v___x_1321_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1321_, 0, lean_box(0));
lean_closure_set(v___x_1321_, 1, lean_box(0));
lean_closure_set(v___x_1321_, 2, v___x_1314_);
v___x_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
lean_ctor_set(v___x_1322_, 2, v___f_1316_);
lean_ctor_set(v___x_1322_, 3, v___f_1317_);
lean_ctor_set(v___x_1322_, 4, v___f_1318_);
v___x_1323_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1323_, 0, lean_box(0));
lean_closure_set(v___x_1323_, 1, lean_box(0));
lean_closure_set(v___x_1323_, 2, v___x_1314_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = lean_box(0);
v___x_1326_ = l_instInhabitedOfMonad___redArg(v___x_1324_, v___x_1325_);
v___f_1327_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1327_, 0, v___x_1326_);
v___x_1423__overap_1328_ = lean_panic_fn_borrowed(v___f_1327_, v_msg_1310_);
lean_dec_ref(v___f_1327_);
lean_inc_ref(v___y_1311_);
v___x_1329_ = lean_apply_3(v___x_1423__overap_1328_, v___y_1311_, v___y_1312_, lean_box(0));
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___boxed(lean_object* v_msg_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v_msg_1330_, v___y_1331_, v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(lean_object* v_a_1335_, lean_object* v_x_1336_){
_start:
{
if (lean_obj_tag(v_x_1336_) == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_box(0);
return v___x_1337_;
}
else
{
lean_object* v_key_1338_; lean_object* v_value_1339_; lean_object* v_tail_1340_; uint8_t v___x_1341_; 
v_key_1338_ = lean_ctor_get(v_x_1336_, 0);
v_value_1339_ = lean_ctor_get(v_x_1336_, 1);
v_tail_1340_ = lean_ctor_get(v_x_1336_, 2);
v___x_1341_ = lean_name_eq(v_key_1338_, v_a_1335_);
if (v___x_1341_ == 0)
{
v_x_1336_ = v_tail_1340_;
goto _start;
}
else
{
lean_object* v___x_1343_; 
lean_inc(v_value_1339_);
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_value_1339_);
return v___x_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg___boxed(lean_object* v_a_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1344_, v_x_1345_);
lean_dec(v_x_1345_);
lean_dec(v_a_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(lean_object* v_m_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_buckets_1349_; lean_object* v___x_1350_; uint64_t v___y_1352_; 
v_buckets_1349_ = lean_ctor_get(v_m_1347_, 1);
v___x_1350_ = lean_array_get_size(v_buckets_1349_);
if (lean_obj_tag(v_a_1348_) == 0)
{
uint64_t v___x_1366_; 
v___x_1366_ = 1723ULL;
v___y_1352_ = v___x_1366_;
goto v___jp_1351_;
}
else
{
uint64_t v_hash_1367_; 
v_hash_1367_ = lean_ctor_get_uint64(v_a_1348_, sizeof(void*)*2);
v___y_1352_ = v_hash_1367_;
goto v___jp_1351_;
}
v___jp_1351_:
{
uint64_t v___x_1353_; uint64_t v___x_1354_; uint64_t v_fold_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; uint64_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1353_ = 32ULL;
v___x_1354_ = lean_uint64_shift_right(v___y_1352_, v___x_1353_);
v_fold_1355_ = lean_uint64_xor(v___y_1352_, v___x_1354_);
v___x_1356_ = 16ULL;
v___x_1357_ = lean_uint64_shift_right(v_fold_1355_, v___x_1356_);
v___x_1358_ = lean_uint64_xor(v_fold_1355_, v___x_1357_);
v___x_1359_ = lean_uint64_to_usize(v___x_1358_);
v___x_1360_ = lean_usize_of_nat(v___x_1350_);
v___x_1361_ = ((size_t)1ULL);
v___x_1362_ = lean_usize_sub(v___x_1360_, v___x_1361_);
v___x_1363_ = lean_usize_land(v___x_1359_, v___x_1362_);
v___x_1364_ = lean_array_uget_borrowed(v_buckets_1349_, v___x_1363_);
v___x_1365_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1348_, v___x_1364_);
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg___boxed(lean_object* v_m_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1368_, v_a_1369_);
lean_dec(v_a_1369_);
lean_dec_ref(v_m_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(lean_object* v_s_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v_putStr_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_get_stdout();
v_putStr_1374_ = lean_ctor_get(v___x_1373_, 4);
lean_inc_ref(v_putStr_1374_);
lean_dec_ref(v___x_1373_);
v___x_1375_ = lean_apply_2(v_putStr_1374_, v_s_1371_, lean_box(0));
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2___boxed(lean_object* v_s_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v_s_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(lean_object* v_s_1379_){
_start:
{
uint32_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = 10;
v___x_1382_ = lean_string_push(v_s_1379_, v___x_1381_);
v___x_1383_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1___boxed(lean_object* v_s_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v_s_1384_);
return v_res_1386_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1391_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1392_ = lean_unsigned_to_nat(18u);
v___x_1393_ = lean_unsigned_to_nat(114u);
v___x_1394_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2));
v___x_1395_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1396_ = l_mkPanicMessageWithDecl(v___x_1395_, v___x_1394_, v___x_1393_, v___x_1392_, v___x_1391_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName(lean_object* v_n_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_visitedNames_1405_; lean_object* v___x_1406_; 
v_visitedNames_1405_ = lean_ctor_get(v_a_1403_, 0);
v___x_1406_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_visitedNames_1405_, v_n_1401_);
if (lean_obj_tag(v___x_1406_) == 1)
{
lean_object* v_val_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_n_1401_);
v_val_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_val_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_val_1407_);
lean_ctor_set(v___x_1411_, 1, v_a_1403_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v_fst_1418_; lean_object* v_snd_1419_; 
lean_dec(v___x_1406_);
v___x_1416_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0));
switch(lean_obj_tag(v_n_1401_))
{
case 0:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4, &l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4);
v___x_1461_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1460_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v_fst_1463_; lean_object* v_snd_1464_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v_fst_1463_ = lean_ctor_get(v_a_1462_, 0);
lean_inc(v_fst_1463_);
v_snd_1464_ = lean_ctor_get(v_a_1462_, 1);
lean_inc(v_snd_1464_);
lean_dec(v_a_1462_);
v_fst_1418_ = v_fst_1463_;
v_snd_1419_ = v_snd_1464_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_a_1465_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1461_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1461_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
case 1:
{
lean_object* v_pre_1473_; lean_object* v_str_1474_; lean_object* v___x_1475_; 
v_pre_1473_ = lean_ctor_get(v_n_1401_, 0);
v_str_1474_ = lean_ctor_get(v_n_1401_, 1);
lean_inc(v_pre_1473_);
v___x_1475_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1473_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1504_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1504_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1504_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_fst_1480_; lean_object* v_snd_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1503_; 
v_fst_1480_ = lean_ctor_get(v_a_1476_, 0);
v_snd_1481_ = lean_ctor_get(v_a_1476_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_a_1476_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1483_ = v_a_1476_;
v_isShared_1484_ = v_isSharedCheck_1503_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_snd_1481_);
lean_inc(v_fst_1480_);
lean_dec(v_a_1476_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1503_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1485_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5));
v___x_1486_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1487_ = l_Lean_JsonNumber_fromNat(v_fst_1480_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set_tag(v___x_1478_, 2);
lean_ctor_set(v___x_1478_, 0, v___x_1487_);
v___x_1489_ = v___x_1478_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 1, v___x_1489_);
lean_ctor_set(v___x_1483_, 0, v___x_1486_);
v___x_1491_ = v___x_1483_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_inc_ref(v_str_1474_);
v___x_1492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_str_1474_);
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1485_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_box(0);
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1491_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_Json_mkObj(v___x_1496_);
lean_dec_ref_known(v___x_1496_, 2);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1485_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v___x_1494_);
v___x_1500_ = l_Lean_Json_mkObj(v___x_1499_);
lean_dec_ref_known(v___x_1499_, 2);
v_fst_1418_ = v___x_1500_;
v_snd_1419_ = v_snd_1481_;
goto v___jp_1417_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1401_, 2);
return v___x_1475_;
}
}
default: 
{
lean_object* v_pre_1505_; lean_object* v_i_1506_; lean_object* v___x_1507_; 
v_pre_1505_ = lean_ctor_get(v_n_1401_, 0);
v_i_1506_ = lean_ctor_get(v_n_1401_, 1);
lean_inc(v_pre_1505_);
v___x_1507_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1505_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1538_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1538_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1538_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_fst_1512_; lean_object* v_snd_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1537_; 
v_fst_1512_ = lean_ctor_get(v_a_1508_, 0);
v_snd_1513_ = lean_ctor_get(v_a_1508_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_a_1508_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1515_ = v_a_1508_;
v_isShared_1516_ = v_isSharedCheck_1537_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_snd_1513_);
lean_inc(v_fst_1512_);
lean_dec(v_a_1508_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1537_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1517_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7));
v___x_1518_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1519_ = l_Lean_JsonNumber_fromNat(v_fst_1512_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 2);
lean_ctor_set(v___x_1510_, 0, v___x_1519_);
v___x_1521_ = v___x_1510_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___x_1521_);
lean_ctor_set(v___x_1515_, 0, v___x_1518_);
v___x_1523_ = v___x_1515_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1524_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8));
lean_inc(v_i_1506_);
v___x_1525_ = l_Lean_JsonNumber_fromNat(v_i_1506_);
v___x_1526_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1524_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = lean_box(0);
v___x_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1523_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = l_Lean_Json_mkObj(v___x_1530_);
lean_dec_ref_known(v___x_1530_, 2);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1517_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___x_1528_);
v___x_1534_ = l_Lean_Json_mkObj(v___x_1533_);
lean_dec_ref_known(v___x_1533_, 2);
v_fst_1418_ = v___x_1534_;
v_snd_1419_ = v_snd_1513_;
goto v___jp_1417_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1401_, 2);
return v___x_1507_;
}
}
}
v___jp_1417_:
{
lean_object* v_visitedNames_1420_; lean_object* v_visitedLevels_1421_; lean_object* v_visitedExprs_1422_; lean_object* v_visitedConstants_1423_; lean_object* v_noMDataExprs_1424_; uint8_t v_exportMData_1425_; uint8_t v_exportUnsafe_1426_; uint8_t v_ignoreMissing_1427_; lean_object* v_recursorMap_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1459_; 
v_visitedNames_1420_ = lean_ctor_get(v_snd_1419_, 0);
v_visitedLevels_1421_ = lean_ctor_get(v_snd_1419_, 1);
v_visitedExprs_1422_ = lean_ctor_get(v_snd_1419_, 2);
v_visitedConstants_1423_ = lean_ctor_get(v_snd_1419_, 3);
v_noMDataExprs_1424_ = lean_ctor_get(v_snd_1419_, 4);
v_exportMData_1425_ = lean_ctor_get_uint8(v_snd_1419_, sizeof(void*)*6);
v_exportUnsafe_1426_ = lean_ctor_get_uint8(v_snd_1419_, sizeof(void*)*6 + 1);
v_ignoreMissing_1427_ = lean_ctor_get_uint8(v_snd_1419_, sizeof(void*)*6 + 2);
v_recursorMap_1428_ = lean_ctor_get(v_snd_1419_, 5);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_snd_1419_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1430_ = v_snd_1419_;
v_isShared_1431_ = v_isSharedCheck_1459_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_recursorMap_1428_);
lean_inc(v_noMDataExprs_1424_);
lean_inc(v_visitedConstants_1423_);
lean_inc(v_visitedExprs_1422_);
lean_inc(v_visitedLevels_1421_);
lean_inc(v_visitedNames_1420_);
lean_dec(v_snd_1419_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1459_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_size_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_size_1432_ = lean_ctor_get(v_visitedNames_1420_, 0);
lean_inc_n(v_size_1432_, 2);
v___x_1433_ = l_Lean_JsonNumber_fromNat(v_size_1432_);
v___x_1434_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
v___x_1435_ = l_Lean_Json_setObjVal_x21(v_fst_1418_, v___x_1416_, v___x_1434_);
v___x_1436_ = l_Lean_Json_compress(v___x_1435_);
v___x_1437_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1436_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1449_; 
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v___x_1437_, 0);
lean_dec(v_unused_1450_);
v___x_1439_ = v___x_1437_;
v_isShared_1440_ = v_isSharedCheck_1449_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v___x_1437_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1449_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
lean_inc(v_size_1432_);
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v_visitedNames_1420_, v_n_1401_, v_size_1432_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1441_);
v___x_1443_ = v___x_1430_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_visitedLevels_1421_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_visitedExprs_1422_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_visitedConstants_1423_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_noMDataExprs_1424_);
lean_ctor_set(v_reuseFailAlloc_1448_, 5, v_recursorMap_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1448_, sizeof(void*)*6, v_exportMData_1425_);
lean_ctor_set_uint8(v_reuseFailAlloc_1448_, sizeof(void*)*6 + 1, v_exportUnsafe_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1448_, sizeof(void*)*6 + 2, v_ignoreMissing_1427_);
v___x_1443_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_size_1432_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1446_ = v___x_1439_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_size_1432_);
lean_del_object(v___x_1430_);
lean_dec(v_recursorMap_1428_);
lean_dec_ref(v_noMDataExprs_1424_);
lean_dec_ref(v_visitedConstants_1423_);
lean_dec_ref(v_visitedExprs_1422_);
lean_dec_ref(v_visitedLevels_1421_);
lean_dec_ref(v_visitedNames_1420_);
lean_dec(v_n_1401_);
v_a_1451_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1437_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1437_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___boxed(lean_object* v_n_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_n_1539_, v_a_1540_, v_a_1541_);
lean_dec_ref(v_a_1540_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(lean_object* v_00_u03b2_1544_, lean_object* v_m_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1545_, v_a_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___boxed(lean_object* v_00_u03b2_1548_, lean_object* v_m_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(v_00_u03b2_1548_, v_m_1549_, v_a_1550_);
lean_dec(v_a_1550_);
lean_dec_ref(v_m_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(lean_object* v_00_u03b2_1552_, lean_object* v_a_1553_, lean_object* v_x_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1553_, v_x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1556_, lean_object* v_a_1557_, lean_object* v_x_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(v_00_u03b2_1556_, v_a_1557_, v_x_1558_);
lean_dec(v_x_1558_);
lean_dec(v_a_1557_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(lean_object* v_a_1560_, lean_object* v_x_1561_){
_start:
{
if (lean_obj_tag(v_x_1561_) == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_box(0);
return v___x_1562_;
}
else
{
lean_object* v_key_1563_; lean_object* v_value_1564_; lean_object* v_tail_1565_; uint8_t v___x_1566_; 
v_key_1563_ = lean_ctor_get(v_x_1561_, 0);
v_value_1564_ = lean_ctor_get(v_x_1561_, 1);
v_tail_1565_ = lean_ctor_get(v_x_1561_, 2);
v___x_1566_ = lean_level_eq(v_key_1563_, v_a_1560_);
if (v___x_1566_ == 0)
{
v_x_1561_ = v_tail_1565_;
goto _start;
}
else
{
lean_object* v___x_1568_; 
lean_inc(v_value_1564_);
v___x_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_value_1564_);
return v___x_1568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg___boxed(lean_object* v_a_1569_, lean_object* v_x_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1569_, v_x_1570_);
lean_dec(v_x_1570_);
lean_dec(v_a_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(lean_object* v_m_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_buckets_1574_; lean_object* v___x_1575_; uint64_t v___x_1576_; uint64_t v___x_1577_; uint64_t v___x_1578_; uint64_t v_fold_1579_; uint64_t v___x_1580_; uint64_t v___x_1581_; uint64_t v___x_1582_; size_t v___x_1583_; size_t v___x_1584_; size_t v___x_1585_; size_t v___x_1586_; size_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_buckets_1574_ = lean_ctor_get(v_m_1572_, 1);
v___x_1575_ = lean_array_get_size(v_buckets_1574_);
v___x_1576_ = l_Lean_Level_hash(v_a_1573_);
v___x_1577_ = 32ULL;
v___x_1578_ = lean_uint64_shift_right(v___x_1576_, v___x_1577_);
v_fold_1579_ = lean_uint64_xor(v___x_1576_, v___x_1578_);
v___x_1580_ = 16ULL;
v___x_1581_ = lean_uint64_shift_right(v_fold_1579_, v___x_1580_);
v___x_1582_ = lean_uint64_xor(v_fold_1579_, v___x_1581_);
v___x_1583_ = lean_uint64_to_usize(v___x_1582_);
v___x_1584_ = lean_usize_of_nat(v___x_1575_);
v___x_1585_ = ((size_t)1ULL);
v___x_1586_ = lean_usize_sub(v___x_1584_, v___x_1585_);
v___x_1587_ = lean_usize_land(v___x_1583_, v___x_1586_);
v___x_1588_ = lean_array_uget_borrowed(v_buckets_1574_, v___x_1587_);
v___x_1589_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1573_, v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg___boxed(lean_object* v_m_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_m_1590_);
return v_res_1592_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1600_ = lean_unsigned_to_nat(23u);
v___x_1601_ = lean_unsigned_to_nat(132u);
v___x_1602_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5));
v___x_1603_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1604_ = l_mkPanicMessageWithDecl(v___x_1603_, v___x_1602_, v___x_1601_, v___x_1600_, v___x_1599_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel(lean_object* v_l_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_visitedLevels_1609_; lean_object* v___x_1610_; 
v_visitedLevels_1609_ = lean_ctor_get(v_a_1607_, 1);
v___x_1610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_visitedLevels_1609_, v_l_1605_);
if (lean_obj_tag(v___x_1610_) == 1)
{
lean_object* v_val_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_l_1605_);
v_val_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_val_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v_val_1611_);
lean_ctor_set(v___x_1615_, 1, v_a_1607_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1615_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
lean_object* v___x_1620_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; 
lean_dec(v___x_1610_);
v___x_1620_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0));
switch(lean_obj_tag(v_l_1605_))
{
case 1:
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v_l_1605_, 0);
lean_inc(v_a_1664_);
v___x_1665_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1664_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1687_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1687_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1687_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_fst_1670_; lean_object* v_snd_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1686_; 
v_fst_1670_ = lean_ctor_get(v_a_1666_, 0);
v_snd_1671_ = lean_ctor_get(v_a_1666_, 1);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_a_1666_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1673_ = v_a_1666_;
v_isShared_1674_ = v_isSharedCheck_1686_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_snd_1671_);
lean_inc(v_fst_1670_);
lean_dec(v_a_1666_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1686_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1675_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1));
v___x_1676_ = l_Lean_JsonNumber_fromNat(v_fst_1670_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 2);
lean_ctor_set(v___x_1668_, 0, v___x_1676_);
v___x_1678_ = v___x_1668_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 1, v___x_1678_);
lean_ctor_set(v___x_1673_, 0, v___x_1675_);
v___x_1680_ = v___x_1673_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_box(0);
v___x_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = l_Lean_Json_mkObj(v___x_1682_);
lean_dec_ref_known(v___x_1682_, 2);
v_fst_1622_ = v___x_1683_;
v_snd_1623_ = v_snd_1671_;
goto v___jp_1621_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1605_, 1);
return v___x_1665_;
}
}
case 2:
{
lean_object* v_a_1688_; lean_object* v_a_1689_; lean_object* v___x_1690_; 
v_a_1688_ = lean_ctor_get(v_l_1605_, 0);
v_a_1689_ = lean_ctor_get(v_l_1605_, 1);
lean_inc(v_a_1688_);
v___x_1690_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1688_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1735_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1735_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1735_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_fst_1695_; lean_object* v_snd_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1734_; 
v_fst_1695_ = lean_ctor_get(v_a_1691_, 0);
v_snd_1696_ = lean_ctor_get(v_a_1691_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_a_1691_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1698_ = v_a_1691_;
v_isShared_1699_ = v_isSharedCheck_1734_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_snd_1696_);
lean_inc(v_fst_1695_);
lean_dec(v_a_1691_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1734_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; 
lean_inc(v_a_1689_);
v___x_1700_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1689_, v_a_1606_, v_snd_1696_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1733_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1733_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1733_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_fst_1705_; lean_object* v_snd_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1732_; 
v_fst_1705_ = lean_ctor_get(v_a_1701_, 0);
v_snd_1706_ = lean_ctor_get(v_a_1701_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_a_1701_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1708_ = v_a_1701_;
v_isShared_1709_ = v_isSharedCheck_1732_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snd_1706_);
lean_inc(v_fst_1705_);
lean_dec(v_a_1701_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1732_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1710_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2));
v___x_1711_ = l_Lean_JsonNumber_fromNat(v_fst_1695_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 2);
lean_ctor_set(v___x_1703_, 0, v___x_1711_);
v___x_1713_ = v___x_1703_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1714_ = l_Lean_JsonNumber_fromNat(v_fst_1705_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 2);
lean_ctor_set(v___x_1693_, 0, v___x_1714_);
v___x_1716_ = v___x_1693_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1717_ = lean_unsigned_to_nat(2u);
v___x_1718_ = lean_mk_empty_array_with_capacity(v___x_1717_);
v___x_1719_ = lean_array_push(v___x_1718_, v___x_1713_);
v___x_1720_ = lean_array_push(v___x_1719_, v___x_1716_);
v___x_1721_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 1, v___x_1721_);
lean_ctor_set(v___x_1708_, 0, v___x_1710_);
v___x_1723_ = v___x_1708_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = lean_box(0);
if (v_isShared_1699_ == 0)
{
lean_ctor_set_tag(v___x_1698_, 1);
lean_ctor_set(v___x_1698_, 1, v___x_1724_);
lean_ctor_set(v___x_1698_, 0, v___x_1723_);
v___x_1726_ = v___x_1698_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Json_mkObj(v___x_1726_);
lean_dec_ref(v___x_1726_);
v_fst_1622_ = v___x_1727_;
v_snd_1623_ = v_snd_1706_;
goto v___jp_1621_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1698_);
lean_dec(v_fst_1695_);
lean_del_object(v___x_1693_);
lean_dec_ref_known(v_l_1605_, 2);
return v___x_1700_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1605_, 2);
return v___x_1690_;
}
}
case 3:
{
lean_object* v_a_1736_; lean_object* v_a_1737_; lean_object* v___x_1738_; 
v_a_1736_ = lean_ctor_get(v_l_1605_, 0);
v_a_1737_ = lean_ctor_get(v_l_1605_, 1);
lean_inc(v_a_1736_);
v___x_1738_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1736_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1783_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1783_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1783_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v_fst_1743_; lean_object* v_snd_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1782_; 
v_fst_1743_ = lean_ctor_get(v_a_1739_, 0);
v_snd_1744_ = lean_ctor_get(v_a_1739_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_a_1739_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1746_ = v_a_1739_;
v_isShared_1747_ = v_isSharedCheck_1782_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_snd_1744_);
lean_inc(v_fst_1743_);
lean_dec(v_a_1739_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1782_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; 
lean_inc(v_a_1737_);
v___x_1748_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1737_, v_a_1606_, v_snd_1744_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1781_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1781_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1781_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1780_; 
v_fst_1753_ = lean_ctor_get(v_a_1749_, 0);
v_snd_1754_ = lean_ctor_get(v_a_1749_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_a_1749_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1756_ = v_a_1749_;
v_isShared_1757_ = v_isSharedCheck_1780_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snd_1754_);
lean_inc(v_fst_1753_);
lean_dec(v_a_1749_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1780_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1758_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3));
v___x_1759_ = l_Lean_JsonNumber_fromNat(v_fst_1743_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 2);
lean_ctor_set(v___x_1751_, 0, v___x_1759_);
v___x_1761_ = v___x_1751_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = l_Lean_JsonNumber_fromNat(v_fst_1753_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 2);
lean_ctor_set(v___x_1741_, 0, v___x_1762_);
v___x_1764_ = v___x_1741_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1765_ = lean_unsigned_to_nat(2u);
v___x_1766_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___x_1767_ = lean_array_push(v___x_1766_, v___x_1761_);
v___x_1768_ = lean_array_push(v___x_1767_, v___x_1764_);
v___x_1769_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___x_1769_);
lean_ctor_set(v___x_1756_, 0, v___x_1758_);
v___x_1771_ = v___x_1756_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = lean_box(0);
if (v_isShared_1747_ == 0)
{
lean_ctor_set_tag(v___x_1746_, 1);
lean_ctor_set(v___x_1746_, 1, v___x_1772_);
lean_ctor_set(v___x_1746_, 0, v___x_1771_);
v___x_1774_ = v___x_1746_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_Json_mkObj(v___x_1774_);
lean_dec_ref(v___x_1774_);
v_fst_1622_ = v___x_1775_;
v_snd_1623_ = v_snd_1754_;
goto v___jp_1621_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1746_);
lean_dec(v_fst_1743_);
lean_del_object(v___x_1741_);
lean_dec_ref_known(v_l_1605_, 2);
return v___x_1748_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1605_, 2);
return v___x_1738_;
}
}
case 4:
{
lean_object* v_a_1784_; lean_object* v___x_1785_; 
v_a_1784_ = lean_ctor_get(v_l_1605_, 0);
lean_inc(v_a_1784_);
v___x_1785_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_a_1784_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1807_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1807_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1807_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1806_; 
v_fst_1790_ = lean_ctor_get(v_a_1786_, 0);
v_snd_1791_ = lean_ctor_get(v_a_1786_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1786_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1793_ = v_a_1786_;
v_isShared_1794_ = v_isSharedCheck_1806_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
lean_dec(v_a_1786_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1806_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1795_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4));
v___x_1796_ = l_Lean_JsonNumber_fromNat(v_fst_1790_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set_tag(v___x_1788_, 2);
lean_ctor_set(v___x_1788_, 0, v___x_1796_);
v___x_1798_ = v___x_1788_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1800_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1798_);
lean_ctor_set(v___x_1793_, 0, v___x_1795_);
v___x_1800_ = v___x_1793_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = l_Lean_Json_mkObj(v___x_1802_);
lean_dec_ref_known(v___x_1802_, 2);
v_fst_1622_ = v___x_1803_;
v_snd_1623_ = v_snd_1791_;
goto v___jp_1621_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1605_, 1);
return v___x_1785_;
}
}
default: 
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6, &l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6);
v___x_1809_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1808_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v_fst_1811_; lean_object* v_snd_1812_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v_fst_1811_ = lean_ctor_get(v_a_1810_, 0);
lean_inc(v_fst_1811_);
v_snd_1812_ = lean_ctor_get(v_a_1810_, 1);
lean_inc(v_snd_1812_);
lean_dec(v_a_1810_);
v_fst_1622_ = v_fst_1811_;
v_snd_1623_ = v_snd_1812_;
goto v___jp_1621_;
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_l_1605_);
v_a_1813_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1809_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1809_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
v___jp_1621_:
{
lean_object* v_visitedLevels_1624_; lean_object* v_visitedNames_1625_; lean_object* v_visitedExprs_1626_; lean_object* v_visitedConstants_1627_; lean_object* v_noMDataExprs_1628_; uint8_t v_exportMData_1629_; uint8_t v_exportUnsafe_1630_; uint8_t v_ignoreMissing_1631_; lean_object* v_recursorMap_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1663_; 
v_visitedLevels_1624_ = lean_ctor_get(v_snd_1623_, 1);
v_visitedNames_1625_ = lean_ctor_get(v_snd_1623_, 0);
v_visitedExprs_1626_ = lean_ctor_get(v_snd_1623_, 2);
v_visitedConstants_1627_ = lean_ctor_get(v_snd_1623_, 3);
v_noMDataExprs_1628_ = lean_ctor_get(v_snd_1623_, 4);
v_exportMData_1629_ = lean_ctor_get_uint8(v_snd_1623_, sizeof(void*)*6);
v_exportUnsafe_1630_ = lean_ctor_get_uint8(v_snd_1623_, sizeof(void*)*6 + 1);
v_ignoreMissing_1631_ = lean_ctor_get_uint8(v_snd_1623_, sizeof(void*)*6 + 2);
v_recursorMap_1632_ = lean_ctor_get(v_snd_1623_, 5);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_snd_1623_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1634_ = v_snd_1623_;
v_isShared_1635_ = v_isSharedCheck_1663_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_recursorMap_1632_);
lean_inc(v_noMDataExprs_1628_);
lean_inc(v_visitedConstants_1627_);
lean_inc(v_visitedExprs_1626_);
lean_inc(v_visitedLevels_1624_);
lean_inc(v_visitedNames_1625_);
lean_dec(v_snd_1623_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1663_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v_size_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_size_1636_ = lean_ctor_get(v_visitedLevels_1624_, 0);
lean_inc_n(v_size_1636_, 2);
v___x_1637_ = l_Lean_JsonNumber_fromNat(v_size_1636_);
v___x_1638_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
v___x_1639_ = l_Lean_Json_setObjVal_x21(v_fst_1622_, v___x_1620_, v___x_1638_);
v___x_1640_ = l_Lean_Json_compress(v___x_1639_);
v___x_1641_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1640_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1653_; 
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; 
v_unused_1654_ = lean_ctor_get(v___x_1641_, 0);
lean_dec(v_unused_1654_);
v___x_1643_ = v___x_1641_;
v_isShared_1644_ = v_isSharedCheck_1653_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v___x_1641_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1653_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
lean_inc(v_size_1636_);
v___x_1645_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v_visitedLevels_1624_, v_l_1605_, v_size_1636_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 1, v___x_1645_);
v___x_1647_ = v___x_1634_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_visitedNames_1625_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_visitedExprs_1626_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_visitedConstants_1627_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_noMDataExprs_1628_);
lean_ctor_set(v_reuseFailAlloc_1652_, 5, v_recursorMap_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1652_, sizeof(void*)*6, v_exportMData_1629_);
lean_ctor_set_uint8(v_reuseFailAlloc_1652_, sizeof(void*)*6 + 1, v_exportUnsafe_1630_);
lean_ctor_set_uint8(v_reuseFailAlloc_1652_, sizeof(void*)*6 + 2, v_ignoreMissing_1631_);
v___x_1647_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_size_1636_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1648_);
v___x_1650_ = v___x_1643_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec(v_size_1636_);
lean_del_object(v___x_1634_);
lean_dec(v_recursorMap_1632_);
lean_dec_ref(v_noMDataExprs_1628_);
lean_dec_ref(v_visitedConstants_1627_);
lean_dec_ref(v_visitedExprs_1626_);
lean_dec_ref(v_visitedNames_1625_);
lean_dec_ref(v_visitedLevels_1624_);
lean_dec(v_l_1605_);
v_a_1655_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1641_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1641_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___boxed(lean_object* v_l_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_l_1821_, v_a_1822_, v_a_1823_);
lean_dec_ref(v_a_1822_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(lean_object* v_00_u03b2_1826_, lean_object* v_m_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1827_, v_a_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___boxed(lean_object* v_00_u03b2_1830_, lean_object* v_m_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(v_00_u03b2_1830_, v_m_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_m_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(lean_object* v_00_u03b2_1834_, lean_object* v_a_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1835_, v_x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1838_, lean_object* v_a_1839_, lean_object* v_x_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(v_00_u03b2_1838_, v_a_1839_, v_x_1840_);
lean_dec(v_x_1840_);
lean_dec(v_a_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
if (lean_obj_tag(v_a_1842_) == 0)
{
lean_object* v___x_1844_; 
v___x_1844_ = l_List_reverse___redArg(v_a_1843_);
return v___x_1844_;
}
else
{
lean_object* v_head_1845_; lean_object* v_tail_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1855_; 
v_head_1845_ = lean_ctor_get(v_a_1842_, 0);
v_tail_1846_ = lean_ctor_get(v_a_1842_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_a_1842_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1848_ = v_a_1842_;
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_tail_1846_);
lean_inc(v_head_1845_);
lean_dec(v_a_1842_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = l_Lean_Level_param___override(v_head_1845_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v_a_1843_);
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_a_1843_);
v___x_1852_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v_a_1842_ = v_tail_1846_;
v_a_1843_ = v___x_1852_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(size_t v_sz_1856_, size_t v_i_1857_, lean_object* v_bs_1858_){
_start:
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_usize_dec_lt(v_i_1857_, v_sz_1856_);
if (v___x_1859_ == 0)
{
return v_bs_1858_;
}
else
{
lean_object* v_v_1860_; lean_object* v___x_1861_; lean_object* v_bs_x27_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v_v_1860_ = lean_array_uget(v_bs_1858_, v_i_1857_);
v___x_1861_ = lean_unsigned_to_nat(0u);
v_bs_x27_1862_ = lean_array_uset(v_bs_1858_, v_i_1857_, v___x_1861_);
v___x_1863_ = l_Lean_JsonNumber_fromNat(v_v_1860_);
v___x_1864_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_i_1857_, v___x_1865_);
v___x_1867_ = lean_array_uset(v_bs_x27_1862_, v_i_1857_, v___x_1864_);
v_i_1857_ = v___x_1866_;
v_bs_1858_ = v___x_1867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1869_, lean_object* v_i_1870_, lean_object* v_bs_1871_){
_start:
{
size_t v_sz_boxed_1872_; size_t v_i_boxed_1873_; lean_object* v_res_1874_; 
v_sz_boxed_1872_ = lean_unbox_usize(v_sz_1869_);
lean_dec(v_sz_1869_);
v_i_boxed_1873_ = lean_unbox_usize(v_i_1870_);
lean_dec(v_i_1870_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_boxed_1872_, v_i_boxed_1873_, v_bs_1871_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(lean_object* v_a_1875_){
_start:
{
size_t v_sz_1876_; size_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_sz_1876_ = lean_array_size(v_a_1875_);
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_1876_, v___x_1877_, v_a_1875_);
v___x_1879_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_array_mk(v_a_1880_);
v___x_1882_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
if (lean_obj_tag(v_x_1883_) == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = l_List_reverse___redArg(v_x_1884_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v___y_1886_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
else
{
lean_object* v_head_1891_; lean_object* v_tail_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1912_; 
v_head_1891_ = lean_ctor_get(v_x_1883_, 0);
v_tail_1892_ = lean_ctor_get(v_x_1883_, 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_x_1883_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1894_ = v_x_1883_;
v_isShared_1895_ = v_isSharedCheck_1912_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_tail_1892_);
lean_inc(v_head_1891_);
lean_dec(v_x_1883_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1912_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; 
v___x_1896_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_head_1891_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v_fst_1898_; lean_object* v_snd_1899_; lean_object* v___x_1901_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v_fst_1898_ = lean_ctor_get(v_a_1897_, 0);
lean_inc(v_fst_1898_);
v_snd_1899_ = lean_ctor_get(v_a_1897_, 1);
lean_inc(v_snd_1899_);
lean_dec(v_a_1897_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v_x_1884_);
lean_ctor_set(v___x_1894_, 0, v_fst_1898_);
v___x_1901_ = v___x_1894_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_fst_1898_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_x_1884_);
v___x_1901_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
v_x_1883_ = v_tail_1892_;
v_x_1884_ = v___x_1901_;
v___y_1886_ = v_snd_1899_;
goto _start;
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_del_object(v___x_1894_);
lean_dec(v_tail_1892_);
lean_dec(v_x_1884_);
v_a_1904_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1896_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1896_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2___boxed(lean_object* v_x_1913_, lean_object* v_x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_x_1913_, v_x_1914_, v___y_1915_, v___y_1916_);
lean_dec_ref(v___y_1915_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = l_List_reverse___redArg(v_x_1920_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v___y_1922_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
else
{
lean_object* v_head_1927_; lean_object* v_tail_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1948_; 
v_head_1927_ = lean_ctor_get(v_x_1919_, 0);
v_tail_1928_ = lean_ctor_get(v_x_1919_, 1);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_x_1919_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1930_ = v_x_1919_;
v_isShared_1931_ = v_isSharedCheck_1948_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_tail_1928_);
lean_inc(v_head_1927_);
lean_dec(v_x_1919_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1948_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; 
v___x_1932_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_head_1927_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v_fst_1934_; lean_object* v_snd_1935_; lean_object* v___x_1937_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v_fst_1934_ = lean_ctor_get(v_a_1933_, 0);
lean_inc(v_fst_1934_);
v_snd_1935_ = lean_ctor_get(v_a_1933_, 1);
lean_inc(v_snd_1935_);
lean_dec(v_a_1933_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v_x_1920_);
lean_ctor_set(v___x_1930_, 0, v_fst_1934_);
v___x_1937_ = v___x_1930_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_fst_1934_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_x_1920_);
v___x_1937_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
v_x_1919_ = v_tail_1928_;
v_x_1920_ = v___x_1937_;
v___y_1922_ = v_snd_1935_;
goto _start;
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_del_object(v___x_1930_);
lean_dec(v_tail_1928_);
lean_dec(v_x_1920_);
v_a_1940_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1932_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1932_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0___boxed(lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_x_1949_, v_x_1950_, v___y_1951_, v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams(lean_object* v_uparams_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_box(0);
lean_inc(v_uparams_1955_);
v___x_1960_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_1955_, v___x_1959_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v_fst_1962_; lean_object* v_snd_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v_fst_1962_ = lean_ctor_get(v_a_1961_, 0);
lean_inc(v_fst_1962_);
v_snd_1963_ = lean_ctor_get(v_a_1961_, 1);
lean_inc(v_snd_1963_);
lean_dec(v_a_1961_);
v___x_1964_ = l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(v_uparams_1955_, v___x_1959_);
v___x_1965_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v___x_1964_, v___x_1959_, v_a_1956_, v_snd_1963_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1983_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1983_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1983_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_snd_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1981_; 
v_snd_1970_ = lean_ctor_get(v_a_1966_, 1);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_a_1966_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v_a_1966_, 0);
lean_dec(v_unused_1982_);
v___x_1972_ = v_a_1966_;
v_isShared_1973_ = v_isSharedCheck_1981_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_snd_1970_);
lean_dec(v_a_1966_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1981_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_1962_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_snd_1970_);
v___x_1976_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1978_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1976_);
v___x_1978_ = v___x_1968_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_fst_1962_);
v_a_1984_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1965_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1965_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_uparams_1955_);
v_a_1992_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1960_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1960_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams___boxed(lean_object* v_uparams_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_uparams_2000_, v_a_2001_, v_a_2002_);
lean_dec_ref(v_a_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames(lean_object* v_uparams_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_2005_, v___x_2009_, v_a_2006_, v_a_2007_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2028_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2028_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2028_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_fst_2015_; lean_object* v_snd_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2027_; 
v_fst_2015_ = lean_ctor_get(v_a_2011_, 0);
v_snd_2016_ = lean_ctor_get(v_a_2011_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_a_2011_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2018_ = v_a_2011_;
v_isShared_2019_ = v_isSharedCheck_2027_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snd_2016_);
lean_inc(v_fst_2015_);
lean_dec(v_a_2011_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2027_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_2015_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_snd_2016_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2022_);
v___x_2024_ = v___x_2013_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_a_2029_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2010_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2010_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames___boxed(lean_object* v_uparams_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_uparams_2037_, v_a_2038_, v_a_2039_);
lean_dec_ref(v_a_2038_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(lean_object* v_msg_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v___f_2047_; lean_object* v___f_2048_; lean_object* v___f_2049_; lean_object* v___f_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___f_2059_; lean_object* v___x_11487__overap_2060_; lean_object* v___x_2061_; 
v___x_2046_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2047_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2047_, 0, v___x_2046_);
v___f_2048_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2048_, 0, v___x_2046_);
v___f_2049_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2049_, 0, v___x_2046_);
v___f_2050_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2050_, 0, v___x_2046_);
v___x_2051_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2051_, 0, lean_box(0));
lean_closure_set(v___x_2051_, 1, lean_box(0));
lean_closure_set(v___x_2051_, 2, v___x_2046_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v___f_2047_);
v___x_2053_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2053_, 0, lean_box(0));
lean_closure_set(v___x_2053_, 1, lean_box(0));
lean_closure_set(v___x_2053_, 2, v___x_2046_);
v___x_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
lean_ctor_set(v___x_2054_, 2, v___f_2048_);
lean_ctor_set(v___x_2054_, 3, v___f_2049_);
lean_ctor_set(v___x_2054_, 4, v___f_2050_);
v___x_2055_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2055_, 0, lean_box(0));
lean_closure_set(v___x_2055_, 1, lean_box(0));
lean_closure_set(v___x_2055_, 2, v___x_2046_);
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2054_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = l_Lean_instInhabitedExpr;
v___x_2058_ = l_instInhabitedOfMonad___redArg(v___x_2056_, v___x_2057_);
v___f_2059_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2059_, 0, v___x_2058_);
v___x_11487__overap_2060_ = lean_panic_fn_borrowed(v___f_2059_, v_msg_2042_);
lean_dec_ref(v___f_2059_);
lean_inc_ref(v___y_2043_);
v___x_2061_ = lean_apply_3(v___x_11487__overap_2060_, v___y_2043_, v___y_2044_, lean_box(0));
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2___boxed(lean_object* v_msg_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v_msg_2062_, v___y_2063_, v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(lean_object* v_a_2067_, lean_object* v_b_2068_, lean_object* v_x_2069_){
_start:
{
if (lean_obj_tag(v_x_2069_) == 0)
{
lean_dec(v_b_2068_);
lean_dec_ref(v_a_2067_);
return v_x_2069_;
}
else
{
lean_object* v_key_2070_; lean_object* v_value_2071_; lean_object* v_tail_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2084_; 
v_key_2070_ = lean_ctor_get(v_x_2069_, 0);
v_value_2071_ = lean_ctor_get(v_x_2069_, 1);
v_tail_2072_ = lean_ctor_get(v_x_2069_, 2);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_x_2069_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2074_ = v_x_2069_;
v_isShared_2075_ = v_isSharedCheck_2084_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_tail_2072_);
lean_inc(v_value_2071_);
lean_inc(v_key_2070_);
lean_dec(v_x_2069_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2084_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_expr_eqv(v_key_2070_, v_a_2067_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2077_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2067_, v_b_2068_, v_tail_2072_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 2, v___x_2077_);
v___x_2079_ = v___x_2074_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_key_2070_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_value_2071_);
lean_ctor_set(v_reuseFailAlloc_2080_, 2, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
else
{
lean_object* v___x_2082_; 
lean_dec(v_value_2071_);
lean_dec(v_key_2070_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v_b_2068_);
lean_ctor_set(v___x_2074_, 0, v_a_2067_);
v___x_2082_ = v___x_2074_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2067_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_b_2068_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_tail_2072_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_2085_, lean_object* v_x_2086_){
_start:
{
if (lean_obj_tag(v_x_2086_) == 0)
{
return v_x_2085_;
}
else
{
lean_object* v_key_2087_; lean_object* v_value_2088_; lean_object* v_tail_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2112_; 
v_key_2087_ = lean_ctor_get(v_x_2086_, 0);
v_value_2088_ = lean_ctor_get(v_x_2086_, 1);
v_tail_2089_ = lean_ctor_get(v_x_2086_, 2);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_x_2086_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2091_ = v_x_2086_;
v_isShared_2092_ = v_isSharedCheck_2112_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_tail_2089_);
lean_inc(v_value_2088_);
lean_inc(v_key_2087_);
lean_dec(v_x_2086_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2112_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; uint64_t v___x_2094_; uint64_t v___x_2095_; uint64_t v___x_2096_; uint64_t v_fold_2097_; uint64_t v___x_2098_; uint64_t v___x_2099_; uint64_t v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2093_ = lean_array_get_size(v_x_2085_);
v___x_2094_ = l_Lean_Expr_hash(v_key_2087_);
v___x_2095_ = 32ULL;
v___x_2096_ = lean_uint64_shift_right(v___x_2094_, v___x_2095_);
v_fold_2097_ = lean_uint64_xor(v___x_2094_, v___x_2096_);
v___x_2098_ = 16ULL;
v___x_2099_ = lean_uint64_shift_right(v_fold_2097_, v___x_2098_);
v___x_2100_ = lean_uint64_xor(v_fold_2097_, v___x_2099_);
v___x_2101_ = lean_uint64_to_usize(v___x_2100_);
v___x_2102_ = lean_usize_of_nat(v___x_2093_);
v___x_2103_ = ((size_t)1ULL);
v___x_2104_ = lean_usize_sub(v___x_2102_, v___x_2103_);
v___x_2105_ = lean_usize_land(v___x_2101_, v___x_2104_);
v___x_2106_ = lean_array_uget_borrowed(v_x_2085_, v___x_2105_);
lean_inc(v___x_2106_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 2, v___x_2106_);
v___x_2108_ = v___x_2091_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_key_2087_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_value_2088_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_array_uset(v_x_2085_, v___x_2105_, v___x_2108_);
v_x_2085_ = v___x_2109_;
v_x_2086_ = v_tail_2089_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(lean_object* v_i_2113_, lean_object* v_source_2114_, lean_object* v_target_2115_){
_start:
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = lean_array_get_size(v_source_2114_);
v___x_2117_ = lean_nat_dec_lt(v_i_2113_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_dec_ref(v_source_2114_);
lean_dec(v_i_2113_);
return v_target_2115_;
}
else
{
lean_object* v_es_2118_; lean_object* v___x_2119_; lean_object* v_source_2120_; lean_object* v_target_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_es_2118_ = lean_array_fget(v_source_2114_, v_i_2113_);
v___x_2119_ = lean_box(0);
v_source_2120_ = lean_array_fset(v_source_2114_, v_i_2113_, v___x_2119_);
v_target_2121_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_target_2115_, v_es_2118_);
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_nat_add(v_i_2113_, v___x_2122_);
lean_dec(v_i_2113_);
v_i_2113_ = v___x_2123_;
v_source_2114_ = v_source_2120_;
v_target_2115_ = v_target_2121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(lean_object* v_data_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v_nbuckets_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2126_ = lean_array_get_size(v_data_2125_);
v___x_2127_ = lean_unsigned_to_nat(2u);
v_nbuckets_2128_ = lean_nat_mul(v___x_2126_, v___x_2127_);
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = lean_box(0);
v___x_2131_ = lean_mk_array(v_nbuckets_2128_, v___x_2130_);
v___x_2132_ = lean_array_propagate_mark(v_data_2125_, v___x_2131_);
v___x_2133_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v___x_2129_, v_data_2125_, v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(lean_object* v_a_2134_, lean_object* v_x_2135_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 0)
{
uint8_t v___x_2136_; 
v___x_2136_ = 0;
return v___x_2136_;
}
else
{
lean_object* v_key_2137_; lean_object* v_tail_2138_; uint8_t v___x_2139_; 
v_key_2137_ = lean_ctor_get(v_x_2135_, 0);
v_tail_2138_ = lean_ctor_get(v_x_2135_, 2);
v___x_2139_ = lean_expr_eqv(v_key_2137_, v_a_2134_);
if (v___x_2139_ == 0)
{
v_x_2135_ = v_tail_2138_;
goto _start;
}
else
{
return v___x_2139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg___boxed(lean_object* v_a_2141_, lean_object* v_x_2142_){
_start:
{
uint8_t v_res_2143_; lean_object* v_r_2144_; 
v_res_2143_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2141_, v_x_2142_);
lean_dec(v_x_2142_);
lean_dec_ref(v_a_2141_);
v_r_2144_ = lean_box(v_res_2143_);
return v_r_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(lean_object* v_m_2145_, lean_object* v_a_2146_, lean_object* v_b_2147_){
_start:
{
lean_object* v_size_2148_; lean_object* v_buckets_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2192_; 
v_size_2148_ = lean_ctor_get(v_m_2145_, 0);
v_buckets_2149_ = lean_ctor_get(v_m_2145_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_m_2145_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2151_ = v_m_2145_;
v_isShared_2152_ = v_isSharedCheck_2192_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_buckets_2149_);
lean_inc(v_size_2148_);
lean_dec(v_m_2145_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2192_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; uint64_t v___x_2154_; uint64_t v___x_2155_; uint64_t v___x_2156_; uint64_t v_fold_2157_; uint64_t v___x_2158_; uint64_t v___x_2159_; uint64_t v___x_2160_; size_t v___x_2161_; size_t v___x_2162_; size_t v___x_2163_; size_t v___x_2164_; size_t v___x_2165_; lean_object* v_bkt_2166_; uint8_t v___x_2167_; 
v___x_2153_ = lean_array_get_size(v_buckets_2149_);
v___x_2154_ = l_Lean_Expr_hash(v_a_2146_);
v___x_2155_ = 32ULL;
v___x_2156_ = lean_uint64_shift_right(v___x_2154_, v___x_2155_);
v_fold_2157_ = lean_uint64_xor(v___x_2154_, v___x_2156_);
v___x_2158_ = 16ULL;
v___x_2159_ = lean_uint64_shift_right(v_fold_2157_, v___x_2158_);
v___x_2160_ = lean_uint64_xor(v_fold_2157_, v___x_2159_);
v___x_2161_ = lean_uint64_to_usize(v___x_2160_);
v___x_2162_ = lean_usize_of_nat(v___x_2153_);
v___x_2163_ = ((size_t)1ULL);
v___x_2164_ = lean_usize_sub(v___x_2162_, v___x_2163_);
v___x_2165_ = lean_usize_land(v___x_2161_, v___x_2164_);
v_bkt_2166_ = lean_array_uget_borrowed(v_buckets_2149_, v___x_2165_);
v___x_2167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2146_, v_bkt_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v_size_x27_2169_; lean_object* v___x_2170_; lean_object* v_buckets_x27_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2168_ = lean_unsigned_to_nat(1u);
v_size_x27_2169_ = lean_nat_add(v_size_2148_, v___x_2168_);
lean_dec(v_size_2148_);
lean_inc(v_bkt_2166_);
v___x_2170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2170_, 0, v_a_2146_);
lean_ctor_set(v___x_2170_, 1, v_b_2147_);
lean_ctor_set(v___x_2170_, 2, v_bkt_2166_);
v_buckets_x27_2171_ = lean_array_uset(v_buckets_2149_, v___x_2165_, v___x_2170_);
v___x_2172_ = lean_unsigned_to_nat(4u);
v___x_2173_ = lean_nat_mul(v_size_x27_2169_, v___x_2172_);
v___x_2174_ = lean_unsigned_to_nat(3u);
v___x_2175_ = lean_nat_div(v___x_2173_, v___x_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_array_get_size(v_buckets_x27_2171_);
v___x_2177_ = lean_nat_dec_le(v___x_2175_, v___x_2176_);
lean_dec(v___x_2175_);
if (v___x_2177_ == 0)
{
lean_object* v_val_2178_; lean_object* v___x_2180_; 
v_val_2178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_buckets_x27_2171_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_val_2178_);
lean_ctor_set(v___x_2151_, 0, v_size_x27_2169_);
v___x_2180_ = v___x_2151_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_size_x27_2169_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_val_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
else
{
lean_object* v___x_2183_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_buckets_x27_2171_);
lean_ctor_set(v___x_2151_, 0, v_size_x27_2169_);
v___x_2183_ = v___x_2151_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_size_x27_2169_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_buckets_x27_2171_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
else
{
lean_object* v___x_2185_; lean_object* v_buckets_x27_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
lean_inc(v_bkt_2166_);
v___x_2185_ = lean_box(0);
v_buckets_x27_2186_ = lean_array_uset(v_buckets_2149_, v___x_2165_, v___x_2185_);
v___x_2187_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2146_, v_b_2147_, v_bkt_2166_);
v___x_2188_ = lean_array_uset(v_buckets_x27_2186_, v___x_2165_, v___x_2187_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v___x_2188_);
v___x_2190_ = v___x_2151_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_size_2148_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(lean_object* v_a_2193_, lean_object* v_x_2194_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_box(0);
return v___x_2195_;
}
else
{
lean_object* v_key_2196_; lean_object* v_value_2197_; lean_object* v_tail_2198_; uint8_t v___x_2199_; 
v_key_2196_ = lean_ctor_get(v_x_2194_, 0);
v_value_2197_ = lean_ctor_get(v_x_2194_, 1);
v_tail_2198_ = lean_ctor_get(v_x_2194_, 2);
v___x_2199_ = lean_expr_eqv(v_key_2196_, v_a_2193_);
if (v___x_2199_ == 0)
{
v_x_2194_ = v_tail_2198_;
goto _start;
}
else
{
lean_object* v___x_2201_; 
lean_inc(v_value_2197_);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v_value_2197_);
return v___x_2201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg___boxed(lean_object* v_a_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2202_, v_x_2203_);
lean_dec(v_x_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(lean_object* v_m_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_buckets_2207_; lean_object* v___x_2208_; uint64_t v___x_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; uint64_t v_fold_2212_; uint64_t v___x_2213_; uint64_t v___x_2214_; uint64_t v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_buckets_2207_ = lean_ctor_get(v_m_2205_, 1);
v___x_2208_ = lean_array_get_size(v_buckets_2207_);
v___x_2209_ = l_Lean_Expr_hash(v_a_2206_);
v___x_2210_ = 32ULL;
v___x_2211_ = lean_uint64_shift_right(v___x_2209_, v___x_2210_);
v_fold_2212_ = lean_uint64_xor(v___x_2209_, v___x_2211_);
v___x_2213_ = 16ULL;
v___x_2214_ = lean_uint64_shift_right(v_fold_2212_, v___x_2213_);
v___x_2215_ = lean_uint64_xor(v_fold_2212_, v___x_2214_);
v___x_2216_ = lean_uint64_to_usize(v___x_2215_);
v___x_2217_ = lean_usize_of_nat(v___x_2208_);
v___x_2218_ = ((size_t)1ULL);
v___x_2219_ = lean_usize_sub(v___x_2217_, v___x_2218_);
v___x_2220_ = lean_usize_land(v___x_2216_, v___x_2219_);
v___x_2221_ = lean_array_uget_borrowed(v_buckets_2207_, v___x_2220_);
v___x_2222_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2206_, v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg___boxed(lean_object* v_m_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2223_, v_a_2224_);
lean_dec_ref(v_a_2224_);
lean_dec_ref(v_m_2223_);
return v_res_2225_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2227_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_2228_ = lean_unsigned_to_nat(26u);
v___x_2229_ = lean_unsigned_to_nat(152u);
v___x_2230_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0));
v___x_2231_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2232_ = l_mkPanicMessageWithDecl(v___x_2231_, v___x_2230_, v___x_2229_, v___x_2228_, v___x_2227_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData(lean_object* v_e_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_e_x27_2238_; lean_object* v_visitedNames_2239_; lean_object* v_visitedLevels_2240_; lean_object* v_visitedExprs_2241_; lean_object* v_visitedConstants_2242_; lean_object* v_noMDataExprs_2243_; uint8_t v_exportMData_2244_; uint8_t v_exportUnsafe_2245_; uint8_t v_ignoreMissing_2246_; lean_object* v_recursorMap_2247_; lean_object* v_e_x27_2253_; lean_object* v___y_2254_; lean_object* v_visitedNames_2264_; lean_object* v_visitedLevels_2265_; lean_object* v_visitedExprs_2266_; lean_object* v_visitedConstants_2267_; lean_object* v_noMDataExprs_2268_; uint8_t v_exportMData_2269_; uint8_t v_exportUnsafe_2270_; uint8_t v_ignoreMissing_2271_; lean_object* v_recursorMap_2272_; lean_object* v___x_2273_; 
v_visitedNames_2264_ = lean_ctor_get(v_a_2235_, 0);
v_visitedLevels_2265_ = lean_ctor_get(v_a_2235_, 1);
v_visitedExprs_2266_ = lean_ctor_get(v_a_2235_, 2);
v_visitedConstants_2267_ = lean_ctor_get(v_a_2235_, 3);
v_noMDataExprs_2268_ = lean_ctor_get(v_a_2235_, 4);
v_exportMData_2269_ = lean_ctor_get_uint8(v_a_2235_, sizeof(void*)*6);
v_exportUnsafe_2270_ = lean_ctor_get_uint8(v_a_2235_, sizeof(void*)*6 + 1);
v_ignoreMissing_2271_ = lean_ctor_get_uint8(v_a_2235_, sizeof(void*)*6 + 2);
v_recursorMap_2272_ = lean_ctor_get(v_a_2235_, 5);
v___x_2273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_noMDataExprs_2268_, v_e_2233_);
if (lean_obj_tag(v___x_2273_) == 1)
{
lean_object* v_val_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref(v_e_2233_);
v_val_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_val_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v_val_2274_);
lean_ctor_set(v___x_2278_, 1, v_a_2235_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set_tag(v___x_2276_, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
else
{
lean_dec(v___x_2273_);
switch(lean_obj_tag(v_e_2233_))
{
case 1:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2284_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2283_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v_fst_2286_; lean_object* v_snd_2287_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v_fst_2286_ = lean_ctor_get(v_a_2285_, 0);
lean_inc(v_fst_2286_);
v_snd_2287_ = lean_ctor_get(v_a_2285_, 1);
lean_inc(v_snd_2287_);
lean_dec(v_a_2285_);
v_e_x27_2253_ = v_fst_2286_;
v___y_2254_ = v_snd_2287_;
goto v___jp_2252_;
}
else
{
lean_dec_ref_known(v_e_2233_, 1);
return v___x_2284_;
}
}
case 2:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2289_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2288_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v_fst_2291_; lean_object* v_snd_2292_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v_fst_2291_ = lean_ctor_get(v_a_2290_, 0);
lean_inc(v_fst_2291_);
v_snd_2292_ = lean_ctor_get(v_a_2290_, 1);
lean_inc(v_snd_2292_);
lean_dec(v_a_2290_);
v_e_x27_2253_ = v_fst_2291_;
v___y_2254_ = v_snd_2292_;
goto v___jp_2252_;
}
else
{
lean_dec_ref_known(v_e_2233_, 1);
return v___x_2289_;
}
}
case 5:
{
lean_object* v_fn_2293_; lean_object* v_arg_2294_; lean_object* v___x_2295_; 
v_fn_2293_ = lean_ctor_get(v_e_2233_, 0);
v_arg_2294_ = lean_ctor_get(v_e_2233_, 1);
lean_inc_ref(v_fn_2293_);
v___x_2295_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_fn_2293_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v_fst_2297_; lean_object* v_snd_2298_; lean_object* v___x_2299_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v_fst_2297_ = lean_ctor_get(v_a_2296_, 0);
lean_inc(v_fst_2297_);
v_snd_2298_ = lean_ctor_get(v_a_2296_, 1);
lean_inc(v_snd_2298_);
lean_dec(v_a_2296_);
lean_inc_ref(v_arg_2294_);
v___x_2299_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_arg_2294_, v_a_2234_, v_snd_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v_fst_2301_; lean_object* v_snd_2302_; size_t v___x_2303_; size_t v___x_2304_; uint8_t v___x_2305_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v_fst_2301_ = lean_ctor_get(v_a_2300_, 0);
lean_inc(v_fst_2301_);
v_snd_2302_ = lean_ctor_get(v_a_2300_, 1);
lean_inc(v_snd_2302_);
lean_dec(v_a_2300_);
v___x_2303_ = lean_ptr_addr(v_fn_2293_);
v___x_2304_ = lean_ptr_addr(v_fst_2297_);
v___x_2305_ = lean_usize_dec_eq(v___x_2303_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Expr_app___override(v_fst_2297_, v_fst_2301_);
v_e_x27_2253_ = v___x_2306_;
v___y_2254_ = v_snd_2302_;
goto v___jp_2252_;
}
else
{
size_t v___x_2307_; size_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2307_ = lean_ptr_addr(v_arg_2294_);
v___x_2308_ = lean_ptr_addr(v_fst_2301_);
v___x_2309_ = lean_usize_dec_eq(v___x_2307_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Expr_app___override(v_fst_2297_, v_fst_2301_);
v_e_x27_2253_ = v___x_2310_;
v___y_2254_ = v_snd_2302_;
goto v___jp_2252_;
}
else
{
lean_dec(v_fst_2301_);
lean_dec(v_fst_2297_);
lean_inc_ref(v_e_2233_);
v_e_x27_2253_ = v_e_2233_;
v___y_2254_ = v_snd_2302_;
goto v___jp_2252_;
}
}
}
else
{
lean_dec(v_fst_2297_);
lean_dec_ref_known(v_e_2233_, 2);
return v___x_2299_;
}
}
else
{
lean_dec_ref_known(v_e_2233_, 2);
return v___x_2295_;
}
}
case 6:
{
lean_object* v_binderName_2311_; lean_object* v_binderType_2312_; lean_object* v_body_2313_; uint8_t v_binderInfo_2314_; lean_object* v___x_2315_; 
v_binderName_2311_ = lean_ctor_get(v_e_2233_, 0);
v_binderType_2312_ = lean_ctor_get(v_e_2233_, 1);
v_body_2313_ = lean_ctor_get(v_e_2233_, 2);
v_binderInfo_2314_ = lean_ctor_get_uint8(v_e_2233_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2312_);
v___x_2315_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2312_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v_fst_2317_; lean_object* v_snd_2318_; lean_object* v___x_2319_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v_fst_2317_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_fst_2317_);
v_snd_2318_ = lean_ctor_get(v_a_2316_, 1);
lean_inc(v_snd_2318_);
lean_dec(v_a_2316_);
lean_inc_ref(v_body_2313_);
v___x_2319_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2313_, v_a_2234_, v_snd_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v_fst_2321_; lean_object* v_snd_2322_; size_t v___x_2323_; size_t v___x_2324_; uint8_t v___x_2325_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v_fst_2321_ = lean_ctor_get(v_a_2320_, 0);
lean_inc(v_fst_2321_);
v_snd_2322_ = lean_ctor_get(v_a_2320_, 1);
lean_inc(v_snd_2322_);
lean_dec(v_a_2320_);
v___x_2323_ = lean_ptr_addr(v_binderType_2312_);
v___x_2324_ = lean_ptr_addr(v_fst_2317_);
v___x_2325_ = lean_usize_dec_eq(v___x_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; 
lean_inc(v_binderName_2311_);
v___x_2326_ = l_Lean_Expr_lam___override(v_binderName_2311_, v_fst_2317_, v_fst_2321_, v_binderInfo_2314_);
v_e_x27_2253_ = v___x_2326_;
v___y_2254_ = v_snd_2322_;
goto v___jp_2252_;
}
else
{
size_t v___x_2327_; size_t v___x_2328_; uint8_t v___x_2329_; 
v___x_2327_ = lean_ptr_addr(v_body_2313_);
v___x_2328_ = lean_ptr_addr(v_fst_2321_);
v___x_2329_ = lean_usize_dec_eq(v___x_2327_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
lean_inc(v_binderName_2311_);
v___x_2330_ = l_Lean_Expr_lam___override(v_binderName_2311_, v_fst_2317_, v_fst_2321_, v_binderInfo_2314_);
v_e_x27_2253_ = v___x_2330_;
v___y_2254_ = v_snd_2322_;
goto v___jp_2252_;
}
else
{
uint8_t v___x_2331_; 
v___x_2331_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2314_, v_binderInfo_2314_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_inc(v_binderName_2311_);
v___x_2332_ = l_Lean_Expr_lam___override(v_binderName_2311_, v_fst_2317_, v_fst_2321_, v_binderInfo_2314_);
v_e_x27_2253_ = v___x_2332_;
v___y_2254_ = v_snd_2322_;
goto v___jp_2252_;
}
else
{
lean_dec(v_fst_2321_);
lean_dec(v_fst_2317_);
lean_inc_ref(v_e_2233_);
v_e_x27_2253_ = v_e_2233_;
v___y_2254_ = v_snd_2322_;
goto v___jp_2252_;
}
}
}
}
else
{
lean_dec(v_fst_2317_);
lean_dec_ref_known(v_e_2233_, 3);
return v___x_2319_;
}
}
else
{
lean_dec_ref_known(v_e_2233_, 3);
return v___x_2315_;
}
}
case 7:
{
lean_object* v_binderName_2333_; lean_object* v_binderType_2334_; lean_object* v_body_2335_; uint8_t v_binderInfo_2336_; lean_object* v___x_2337_; 
v_binderName_2333_ = lean_ctor_get(v_e_2233_, 0);
v_binderType_2334_ = lean_ctor_get(v_e_2233_, 1);
v_body_2335_ = lean_ctor_get(v_e_2233_, 2);
v_binderInfo_2336_ = lean_ctor_get_uint8(v_e_2233_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2334_);
v___x_2337_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2334_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v_fst_2339_; lean_object* v_snd_2340_; lean_object* v___x_2341_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v_fst_2339_ = lean_ctor_get(v_a_2338_, 0);
lean_inc(v_fst_2339_);
v_snd_2340_ = lean_ctor_get(v_a_2338_, 1);
lean_inc(v_snd_2340_);
lean_dec(v_a_2338_);
lean_inc_ref(v_body_2335_);
v___x_2341_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2335_, v_a_2234_, v_snd_2340_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v_fst_2343_; lean_object* v_snd_2344_; size_t v___x_2345_; size_t v___x_2346_; uint8_t v___x_2347_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v_fst_2343_ = lean_ctor_get(v_a_2342_, 0);
lean_inc(v_fst_2343_);
v_snd_2344_ = lean_ctor_get(v_a_2342_, 1);
lean_inc(v_snd_2344_);
lean_dec(v_a_2342_);
v___x_2345_ = lean_ptr_addr(v_binderType_2334_);
v___x_2346_ = lean_ptr_addr(v_fst_2339_);
v___x_2347_ = lean_usize_dec_eq(v___x_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_inc(v_binderName_2333_);
v___x_2348_ = l_Lean_Expr_forallE___override(v_binderName_2333_, v_fst_2339_, v_fst_2343_, v_binderInfo_2336_);
v_e_x27_2253_ = v___x_2348_;
v___y_2254_ = v_snd_2344_;
goto v___jp_2252_;
}
else
{
size_t v___x_2349_; size_t v___x_2350_; uint8_t v___x_2351_; 
v___x_2349_ = lean_ptr_addr(v_body_2335_);
v___x_2350_ = lean_ptr_addr(v_fst_2343_);
v___x_2351_ = lean_usize_dec_eq(v___x_2349_, v___x_2350_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
lean_inc(v_binderName_2333_);
v___x_2352_ = l_Lean_Expr_forallE___override(v_binderName_2333_, v_fst_2339_, v_fst_2343_, v_binderInfo_2336_);
v_e_x27_2253_ = v___x_2352_;
v___y_2254_ = v_snd_2344_;
goto v___jp_2252_;
}
else
{
uint8_t v___x_2353_; 
v___x_2353_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2336_, v_binderInfo_2336_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_inc(v_binderName_2333_);
v___x_2354_ = l_Lean_Expr_forallE___override(v_binderName_2333_, v_fst_2339_, v_fst_2343_, v_binderInfo_2336_);
v_e_x27_2253_ = v___x_2354_;
v___y_2254_ = v_snd_2344_;
goto v___jp_2252_;
}
else
{
lean_dec(v_fst_2343_);
lean_dec(v_fst_2339_);
lean_inc_ref(v_e_2233_);
v_e_x27_2253_ = v_e_2233_;
v___y_2254_ = v_snd_2344_;
goto v___jp_2252_;
}
}
}
}
else
{
lean_dec(v_fst_2339_);
lean_dec_ref_known(v_e_2233_, 3);
return v___x_2341_;
}
}
else
{
lean_dec_ref_known(v_e_2233_, 3);
return v___x_2337_;
}
}
case 8:
{
lean_object* v_declName_2355_; lean_object* v_type_2356_; lean_object* v_value_2357_; lean_object* v_body_2358_; uint8_t v_nondep_2359_; lean_object* v___x_2360_; 
v_declName_2355_ = lean_ctor_get(v_e_2233_, 0);
v_type_2356_ = lean_ctor_get(v_e_2233_, 1);
v_value_2357_ = lean_ctor_get(v_e_2233_, 2);
v_body_2358_ = lean_ctor_get(v_e_2233_, 3);
v_nondep_2359_ = lean_ctor_get_uint8(v_e_2233_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2356_);
v___x_2360_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_type_2356_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v_fst_2362_; lean_object* v_snd_2363_; lean_object* v___x_2364_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v_fst_2362_ = lean_ctor_get(v_a_2361_, 0);
lean_inc(v_fst_2362_);
v_snd_2363_ = lean_ctor_get(v_a_2361_, 1);
lean_inc(v_snd_2363_);
lean_dec(v_a_2361_);
lean_inc_ref(v_value_2357_);
v___x_2364_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_value_2357_, v_a_2234_, v_snd_2363_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v_fst_2366_; lean_object* v_snd_2367_; lean_object* v___x_2368_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v_fst_2366_ = lean_ctor_get(v_a_2365_, 0);
lean_inc(v_fst_2366_);
v_snd_2367_ = lean_ctor_get(v_a_2365_, 1);
lean_inc(v_snd_2367_);
lean_dec(v_a_2365_);
lean_inc_ref(v_body_2358_);
v___x_2368_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2358_, v_a_2234_, v_snd_2367_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v_fst_2370_; lean_object* v_snd_2371_; uint8_t v___x_2372_; size_t v___x_2373_; size_t v___x_2374_; uint8_t v___x_2375_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2368_, 1);
v_fst_2370_ = lean_ctor_get(v_a_2369_, 0);
lean_inc(v_fst_2370_);
v_snd_2371_ = lean_ctor_get(v_a_2369_, 1);
lean_inc(v_snd_2371_);
lean_dec(v_a_2369_);
v___x_2372_ = 0;
v___x_2373_ = lean_ptr_addr(v_type_2356_);
v___x_2374_ = lean_ptr_addr(v_fst_2362_);
v___x_2375_ = lean_usize_dec_eq(v___x_2373_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
lean_inc(v_declName_2355_);
v___x_2376_ = l_Lean_Expr_letE___override(v_declName_2355_, v_fst_2362_, v_fst_2366_, v_fst_2370_, v___x_2372_);
v_e_x27_2253_ = v___x_2376_;
v___y_2254_ = v_snd_2371_;
goto v___jp_2252_;
}
else
{
size_t v___x_2377_; size_t v___x_2378_; uint8_t v___x_2379_; 
v___x_2377_ = lean_ptr_addr(v_value_2357_);
v___x_2378_ = lean_ptr_addr(v_fst_2366_);
v___x_2379_ = lean_usize_dec_eq(v___x_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_inc(v_declName_2355_);
v___x_2380_ = l_Lean_Expr_letE___override(v_declName_2355_, v_fst_2362_, v_fst_2366_, v_fst_2370_, v___x_2372_);
v_e_x27_2253_ = v___x_2380_;
v___y_2254_ = v_snd_2371_;
goto v___jp_2252_;
}
else
{
size_t v___x_2381_; size_t v___x_2382_; uint8_t v___x_2383_; 
v___x_2381_ = lean_ptr_addr(v_body_2358_);
v___x_2382_ = lean_ptr_addr(v_fst_2370_);
v___x_2383_ = lean_usize_dec_eq(v___x_2381_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; 
lean_inc(v_declName_2355_);
v___x_2384_ = l_Lean_Expr_letE___override(v_declName_2355_, v_fst_2362_, v_fst_2366_, v_fst_2370_, v___x_2372_);
v_e_x27_2253_ = v___x_2384_;
v___y_2254_ = v_snd_2371_;
goto v___jp_2252_;
}
else
{
if (v_nondep_2359_ == 0)
{
lean_dec(v_fst_2370_);
lean_dec(v_fst_2366_);
lean_dec(v_fst_2362_);
lean_inc_ref(v_e_2233_);
v_e_x27_2253_ = v_e_2233_;
v___y_2254_ = v_snd_2371_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2385_; 
lean_inc(v_declName_2355_);
v___x_2385_ = l_Lean_Expr_letE___override(v_declName_2355_, v_fst_2362_, v_fst_2366_, v_fst_2370_, v___x_2372_);
v_e_x27_2253_ = v___x_2385_;
v___y_2254_ = v_snd_2371_;
goto v___jp_2252_;
}
}
}
}
}
else
{
lean_dec(v_fst_2366_);
lean_dec(v_fst_2362_);
lean_dec_ref_known(v_e_2233_, 4);
return v___x_2368_;
}
}
else
{
lean_dec(v_fst_2362_);
lean_dec_ref_known(v_e_2233_, 4);
return v___x_2364_;
}
}
else
{
lean_dec_ref_known(v_e_2233_, 4);
return v___x_2360_;
}
}
case 10:
{
lean_object* v_expr_2386_; lean_object* v___x_2387_; 
v_expr_2386_ = lean_ctor_get(v_e_2233_, 1);
lean_inc_ref(v_expr_2386_);
v___x_2387_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_expr_2386_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v_fst_2389_; lean_object* v_snd_2390_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v_fst_2389_ = lean_ctor_get(v_a_2388_, 0);
lean_inc(v_fst_2389_);
v_snd_2390_ = lean_ctor_get(v_a_2388_, 1);
lean_inc(v_snd_2390_);
lean_dec(v_a_2388_);
v_e_x27_2253_ = v_fst_2389_;
v___y_2254_ = v_snd_2390_;
goto v___jp_2252_;
}
else
{
lean_dec_ref_known(v_e_2233_, 2);
return v___x_2387_;
}
}
case 11:
{
lean_object* v_typeName_2391_; lean_object* v_idx_2392_; lean_object* v_struct_2393_; lean_object* v___x_2394_; 
v_typeName_2391_ = lean_ctor_get(v_e_2233_, 0);
v_idx_2392_ = lean_ctor_get(v_e_2233_, 1);
v_struct_2393_ = lean_ctor_get(v_e_2233_, 2);
lean_inc_ref(v_struct_2393_);
v___x_2394_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_struct_2393_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; size_t v___x_2398_; size_t v___x_2399_; uint8_t v___x_2400_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v_fst_2396_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_fst_2396_);
v_snd_2397_ = lean_ctor_get(v_a_2395_, 1);
lean_inc(v_snd_2397_);
lean_dec(v_a_2395_);
v___x_2398_ = lean_ptr_addr(v_struct_2393_);
v___x_2399_ = lean_ptr_addr(v_fst_2396_);
v___x_2400_ = lean_usize_dec_eq(v___x_2398_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
lean_inc(v_idx_2392_);
lean_inc(v_typeName_2391_);
v___x_2401_ = l_Lean_Expr_proj___override(v_typeName_2391_, v_idx_2392_, v_fst_2396_);
v_e_x27_2253_ = v___x_2401_;
v___y_2254_ = v_snd_2397_;
goto v___jp_2252_;
}
else
{
lean_dec(v_fst_2396_);
lean_inc_ref(v_e_2233_);
v_e_x27_2253_ = v_e_2233_;
v___y_2254_ = v_snd_2397_;
goto v___jp_2252_;
}
}
else
{
lean_dec_ref_known(v_e_2233_, 3);
return v___x_2394_;
}
}
default: 
{
lean_inc(v_recursorMap_2272_);
lean_inc_ref(v_noMDataExprs_2268_);
lean_inc_ref(v_visitedConstants_2267_);
lean_inc_ref(v_visitedExprs_2266_);
lean_inc_ref(v_visitedLevels_2265_);
lean_inc_ref(v_visitedNames_2264_);
lean_dec_ref(v_a_2235_);
lean_inc_ref(v_e_2233_);
v_e_x27_2238_ = v_e_2233_;
v_visitedNames_2239_ = v_visitedNames_2264_;
v_visitedLevels_2240_ = v_visitedLevels_2265_;
v_visitedExprs_2241_ = v_visitedExprs_2266_;
v_visitedConstants_2242_ = v_visitedConstants_2267_;
v_noMDataExprs_2243_ = v_noMDataExprs_2268_;
v_exportMData_2244_ = v_exportMData_2269_;
v_exportUnsafe_2245_ = v_exportUnsafe_2270_;
v_ignoreMissing_2246_ = v_ignoreMissing_2271_;
v_recursorMap_2247_ = v_recursorMap_2272_;
goto v___jp_2237_;
}
}
}
v___jp_2237_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_inc_ref(v_e_x27_2238_);
v___x_2248_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_noMDataExprs_2243_, v_e_2233_, v_e_x27_2238_);
v___x_2249_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_2249_, 0, v_visitedNames_2239_);
lean_ctor_set(v___x_2249_, 1, v_visitedLevels_2240_);
lean_ctor_set(v___x_2249_, 2, v_visitedExprs_2241_);
lean_ctor_set(v___x_2249_, 3, v_visitedConstants_2242_);
lean_ctor_set(v___x_2249_, 4, v___x_2248_);
lean_ctor_set(v___x_2249_, 5, v_recursorMap_2247_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*6, v_exportMData_2244_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*6 + 1, v_exportUnsafe_2245_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*6 + 2, v_ignoreMissing_2246_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_e_x27_2238_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
v___jp_2252_:
{
lean_object* v_visitedNames_2255_; lean_object* v_visitedLevels_2256_; lean_object* v_visitedExprs_2257_; lean_object* v_visitedConstants_2258_; lean_object* v_noMDataExprs_2259_; uint8_t v_exportMData_2260_; uint8_t v_exportUnsafe_2261_; uint8_t v_ignoreMissing_2262_; lean_object* v_recursorMap_2263_; 
v_visitedNames_2255_ = lean_ctor_get(v___y_2254_, 0);
lean_inc_ref(v_visitedNames_2255_);
v_visitedLevels_2256_ = lean_ctor_get(v___y_2254_, 1);
lean_inc_ref(v_visitedLevels_2256_);
v_visitedExprs_2257_ = lean_ctor_get(v___y_2254_, 2);
lean_inc_ref(v_visitedExprs_2257_);
v_visitedConstants_2258_ = lean_ctor_get(v___y_2254_, 3);
lean_inc_ref(v_visitedConstants_2258_);
v_noMDataExprs_2259_ = lean_ctor_get(v___y_2254_, 4);
lean_inc_ref(v_noMDataExprs_2259_);
v_exportMData_2260_ = lean_ctor_get_uint8(v___y_2254_, sizeof(void*)*6);
v_exportUnsafe_2261_ = lean_ctor_get_uint8(v___y_2254_, sizeof(void*)*6 + 1);
v_ignoreMissing_2262_ = lean_ctor_get_uint8(v___y_2254_, sizeof(void*)*6 + 2);
v_recursorMap_2263_ = lean_ctor_get(v___y_2254_, 5);
lean_inc(v_recursorMap_2263_);
lean_dec_ref(v___y_2254_);
v_e_x27_2238_ = v_e_x27_2253_;
v_visitedNames_2239_ = v_visitedNames_2255_;
v_visitedLevels_2240_ = v_visitedLevels_2256_;
v_visitedExprs_2241_ = v_visitedExprs_2257_;
v_visitedConstants_2242_ = v_visitedConstants_2258_;
v_noMDataExprs_2243_ = v_noMDataExprs_2259_;
v_exportMData_2244_ = v_exportMData_2260_;
v_exportUnsafe_2245_ = v_exportUnsafe_2261_;
v_ignoreMissing_2246_ = v_ignoreMissing_2262_;
v_recursorMap_2247_ = v_recursorMap_2263_;
goto v___jp_2237_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___boxed(lean_object* v_e_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_2402_, v_a_2403_, v_a_2404_);
lean_dec_ref(v_a_2403_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0(lean_object* v_00_u03b2_2407_, lean_object* v_m_2408_, lean_object* v_a_2409_, lean_object* v_b_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_m_2408_, v_a_2409_, v_b_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(lean_object* v_00_u03b2_2412_, lean_object* v_m_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2413_, v_a_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___boxed(lean_object* v_00_u03b2_2416_, lean_object* v_m_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(v_00_u03b2_2416_, v_m_2417_, v_a_2418_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_m_2417_);
return v_res_2419_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(lean_object* v_00_u03b2_2420_, lean_object* v_a_2421_, lean_object* v_x_2422_){
_start:
{
uint8_t v___x_2423_; 
v___x_2423_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2421_, v_x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2424_, lean_object* v_a_2425_, lean_object* v_x_2426_){
_start:
{
uint8_t v_res_2427_; lean_object* v_r_2428_; 
v_res_2427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(v_00_u03b2_2424_, v_a_2425_, v_x_2426_);
lean_dec(v_x_2426_);
lean_dec_ref(v_a_2425_);
v_r_2428_ = lean_box(v_res_2427_);
return v_r_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1(lean_object* v_00_u03b2_2429_, lean_object* v_data_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_data_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2(lean_object* v_00_u03b2_2432_, lean_object* v_a_2433_, lean_object* v_b_2434_, lean_object* v_x_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2433_, v_b_2434_, v_x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(lean_object* v_00_u03b2_2437_, lean_object* v_a_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2438_, v_x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2441_, lean_object* v_a_2442_, lean_object* v_x_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(v_00_u03b2_2441_, v_a_2442_, v_x_2443_);
lean_dec(v_x_2443_);
lean_dec_ref(v_a_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2445_, lean_object* v_i_2446_, lean_object* v_source_2447_, lean_object* v_target_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v_i_2446_, v_source_2447_, v_target_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2450_, lean_object* v_x_2451_, lean_object* v_x_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_x_2451_, v_x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(lean_object* v_fields_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = l_Lean_Json_mkObj(v_fields_2454_);
v___x_2458_ = l_Lean_Json_compress(v___x_2457_);
v___x_2459_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_2458_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2468_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_a_2460_);
lean_ctor_set(v___x_2464_, 1, v_a_2455_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2464_);
v___x_2466_ = v___x_2462_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_a_2455_);
v_a_2469_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2459_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2459_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg___boxed(lean_object* v_fields_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2477_, v_a_2478_);
lean_dec(v_fields_2477_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(lean_object* v_fields_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2481_, v_a_2483_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___boxed(lean_object* v_fields_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(v_fields_2486_, v_a_2487_, v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_fields_2486_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object* v_t_2491_, lean_object* v_k_2492_){
_start:
{
if (lean_obj_tag(v_t_2491_) == 0)
{
lean_object* v_k_2493_; lean_object* v_v_2494_; lean_object* v_l_2495_; lean_object* v_r_2496_; uint8_t v___x_2497_; 
v_k_2493_ = lean_ctor_get(v_t_2491_, 1);
v_v_2494_ = lean_ctor_get(v_t_2491_, 2);
v_l_2495_ = lean_ctor_get(v_t_2491_, 3);
v_r_2496_ = lean_ctor_get(v_t_2491_, 4);
v___x_2497_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2492_, v_k_2493_);
switch(v___x_2497_)
{
case 0:
{
v_t_2491_ = v_l_2495_;
goto _start;
}
case 1:
{
lean_object* v___x_2499_; 
lean_inc(v_v_2494_);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_v_2494_);
return v___x_2499_;
}
default: 
{
v_t_2491_ = v_r_2496_;
goto _start;
}
}
}
else
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_box(0);
return v___x_2501_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object* v_t_2502_, lean_object* v_k_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_2502_, v_k_2503_);
lean_dec(v_k_2503_);
lean_dec(v_t_2502_);
return v_res_2504_;
}
}
static lean_object* _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Array_instInhabited___redArg();
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object* v_msg_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2510_; lean_object* v___f_2511_; lean_object* v___f_2512_; lean_object* v___f_2513_; lean_object* v___f_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___f_2524_; lean_object* v___x_163499__overap_2525_; lean_object* v___x_2526_; 
v___x_2510_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2511_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2511_, 0, v___x_2510_);
v___f_2512_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2512_, 0, v___x_2510_);
v___f_2513_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2513_, 0, v___x_2510_);
v___f_2514_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2514_, 0, v___x_2510_);
v___x_2515_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2515_, 0, lean_box(0));
lean_closure_set(v___x_2515_, 1, lean_box(0));
lean_closure_set(v___x_2515_, 2, v___x_2510_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
lean_ctor_set(v___x_2516_, 1, v___f_2511_);
v___x_2517_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2517_, 0, lean_box(0));
lean_closure_set(v___x_2517_, 1, lean_box(0));
lean_closure_set(v___x_2517_, 2, v___x_2510_);
v___x_2518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
lean_ctor_set(v___x_2518_, 2, v___f_2512_);
lean_ctor_set(v___x_2518_, 3, v___f_2513_);
lean_ctor_set(v___x_2518_, 4, v___f_2514_);
v___x_2519_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2519_, 0, lean_box(0));
lean_closure_set(v___x_2519_, 1, lean_box(0));
lean_closure_set(v___x_2519_, 2, v___x_2510_);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
v___x_2523_ = l_instInhabitedOfMonad___redArg(v___x_2520_, v___x_2522_);
v___f_2524_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2524_, 0, v___x_2523_);
v___x_163499__overap_2525_ = lean_panic_fn_borrowed(v___f_2524_, v_msg_2506_);
lean_dec_ref(v___f_2524_);
lean_inc_ref(v___y_2507_);
v___x_2526_ = lean_apply_3(v___x_163499__overap_2525_, v___y_2507_, v___y_2508_, lean_box(0));
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object* v_msg_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v_msg_2527_, v___y_2528_, v___y_2529_);
lean_dec_ref(v___y_2528_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object* v_msg_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v___f_2537_; lean_object* v___f_2538_; lean_object* v___f_2539_; lean_object* v___f_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___f_2549_; lean_object* v___x_162777__overap_2550_; lean_object* v___x_2551_; 
v___x_2536_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2537_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2537_, 0, v___x_2536_);
v___f_2538_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2538_, 0, v___x_2536_);
v___f_2539_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2539_, 0, v___x_2536_);
v___f_2540_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2540_, 0, v___x_2536_);
v___x_2541_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2541_, 0, lean_box(0));
lean_closure_set(v___x_2541_, 1, lean_box(0));
lean_closure_set(v___x_2541_, 2, v___x_2536_);
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v___f_2537_);
v___x_2543_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2543_, 0, lean_box(0));
lean_closure_set(v___x_2543_, 1, lean_box(0));
lean_closure_set(v___x_2543_, 2, v___x_2536_);
v___x_2544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
lean_ctor_set(v___x_2544_, 2, v___f_2538_);
lean_ctor_set(v___x_2544_, 3, v___f_2539_);
lean_ctor_set(v___x_2544_, 4, v___f_2540_);
v___x_2545_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2545_, 0, lean_box(0));
lean_closure_set(v___x_2545_, 1, lean_box(0));
lean_closure_set(v___x_2545_, 2, v___x_2536_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_box(0);
v___x_2548_ = l_instInhabitedOfMonad___redArg(v___x_2546_, v___x_2547_);
v___f_2549_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2549_, 0, v___x_2548_);
v___x_162777__overap_2550_ = lean_panic_fn_borrowed(v___f_2549_, v_msg_2532_);
lean_dec_ref(v___f_2549_);
lean_inc_ref(v___y_2533_);
v___x_2551_ = lean_apply_3(v___x_162777__overap_2550_, v___y_2533_, v___y_2534_, lean_box(0));
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object* v_msg_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v_msg_2552_, v___y_2553_, v___y_2554_);
lean_dec_ref(v___y_2553_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object* v_msg_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = l_Lean_instInhabitedConstantInfo_default;
v___x_2559_ = lean_panic_fn_borrowed(v___x_2558_, v_msg_2557_);
return v___x_2559_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2562_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1));
v___x_2563_ = lean_unsigned_to_nat(10u);
v___x_2564_ = lean_unsigned_to_nat(334u);
v___x_2565_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2566_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2567_ = l_mkPanicMessageWithDecl(v___x_2566_, v___x_2565_, v___x_2564_, v___x_2563_, v___x_2562_);
return v___x_2567_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2569_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3));
v___x_2570_ = lean_unsigned_to_nat(15u);
v___x_2571_ = lean_unsigned_to_nat(336u);
v___x_2572_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2573_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2574_ = l_mkPanicMessageWithDecl(v___x_2573_, v___x_2572_, v___x_2571_, v___x_2570_, v___x_2569_);
return v___x_2574_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2578_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7));
v___x_2579_ = lean_unsigned_to_nat(14u);
v___x_2580_ = lean_unsigned_to_nat(22u);
v___x_2581_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6));
v___x_2582_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5));
v___x_2583_ = l_mkPanicMessageWithDecl(v___x_2582_, v___x_2581_, v___x_2580_, v___x_2579_, v___x_2578_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t v___y_2584_, uint8_t v___x_2585_, lean_object* v_as_x27_2586_, lean_object* v_b_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
if (lean_obj_tag(v_as_x27_2586_) == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_b_2587_);
lean_ctor_set(v___x_2591_, 1, v___y_2589_);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
else
{
lean_object* v_head_2593_; lean_object* v_tail_2594_; lean_object* v___y_2596_; lean_object* v___y_2600_; lean_object* v___y_2635_; lean_object* v___x_2651_; 
v_head_2593_ = lean_ctor_get(v_as_x27_2586_, 0);
v_tail_2594_ = lean_ctor_get(v_as_x27_2586_, 1);
lean_inc(v_head_2593_);
lean_inc_ref(v___y_2588_);
v___x_2651_ = l_Lean_Environment_find_x3f(v___y_2588_, v_head_2593_, v___x_2585_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_2653_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2652_);
v___y_2635_ = v___x_2653_;
goto v___jp_2634_;
}
else
{
lean_object* v_val_2654_; 
v_val_2654_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_val_2654_);
lean_dec_ref_known(v___x_2651_, 1);
v___y_2635_ = v_val_2654_;
goto v___jp_2634_;
}
v___jp_2595_:
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_array_push(v_b_2587_, v___y_2596_);
v_as_x27_2586_ = v_tail_2594_;
v_b_2587_ = v___x_2597_;
goto _start;
}
v___jp_2599_:
{
uint8_t v_exportUnsafe_2601_; 
v_exportUnsafe_2601_ = lean_ctor_get_uint8(v___y_2589_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_dec_ref(v___y_2600_);
lean_dec_ref(v_b_2587_);
v___x_2602_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2);
v___x_2603_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v___x_2602_, v___y_2588_, v___y_2589_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2625_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2625_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2625_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_fst_2608_; 
v_fst_2608_ = lean_ctor_get(v_a_2604_, 0);
lean_inc(v_fst_2608_);
if (lean_obj_tag(v_fst_2608_) == 0)
{
lean_object* v_snd_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2620_; 
v_snd_2609_ = lean_ctor_get(v_a_2604_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_a_2604_);
if (v_isSharedCheck_2620_ == 0)
{
lean_object* v_unused_2621_; 
v_unused_2621_ = lean_ctor_get(v_a_2604_, 0);
lean_dec(v_unused_2621_);
v___x_2611_ = v_a_2604_;
v_isShared_2612_ = v_isSharedCheck_2620_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_snd_2609_);
lean_dec(v_a_2604_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2620_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v_a_2613_; lean_object* v___x_2615_; 
v_a_2613_ = lean_ctor_get(v_fst_2608_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v_fst_2608_, 1);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v_a_2613_);
v___x_2615_ = v___x_2611_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_snd_2609_);
v___x_2615_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2615_);
v___x_2617_ = v___x_2606_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_snd_2622_; lean_object* v_a_2623_; 
lean_del_object(v___x_2606_);
v_snd_2622_ = lean_ctor_get(v_a_2604_, 1);
lean_inc(v_snd_2622_);
lean_dec(v_a_2604_);
v_a_2623_ = lean_ctor_get(v_fst_2608_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v_fst_2608_, 1);
v_as_x27_2586_ = v_tail_2594_;
v_b_2587_ = v_a_2623_;
v___y_2589_ = v_snd_2622_;
goto _start;
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
v_a_2626_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2603_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2603_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
else
{
v___y_2596_ = v___y_2600_;
goto v___jp_2595_;
}
}
v___jp_2634_:
{
if (lean_obj_tag(v___y_2635_) == 6)
{
lean_object* v_val_2636_; uint8_t v_isUnsafe_2637_; 
v_val_2636_ = lean_ctor_get(v___y_2635_, 0);
lean_inc_ref(v_val_2636_);
lean_dec_ref_known(v___y_2635_, 1);
v_isUnsafe_2637_ = lean_ctor_get_uint8(v_val_2636_, sizeof(void*)*5);
if (v_isUnsafe_2637_ == 0)
{
if (v___y_2584_ == 0)
{
v___y_2600_ = v_val_2636_;
goto v___jp_2599_;
}
else
{
v___y_2596_ = v_val_2636_;
goto v___jp_2595_;
}
}
else
{
v___y_2600_ = v_val_2636_;
goto v___jp_2599_;
}
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_dec_ref(v___y_2635_);
v___x_2638_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4);
v___x_2639_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2638_, v___y_2588_, v___y_2589_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v_snd_2641_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v_snd_2641_ = lean_ctor_get(v_a_2640_, 1);
lean_inc(v_snd_2641_);
lean_dec(v_a_2640_);
v_as_x27_2586_ = v_tail_2594_;
v___y_2589_ = v_snd_2641_;
goto _start;
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v_b_2587_);
v_a_2643_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2639_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2639_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object* v___y_2655_, lean_object* v___x_2656_, lean_object* v_as_x27_2657_, lean_object* v_b_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
uint8_t v___y_172148__boxed_2662_; uint8_t v___x_172149__boxed_2663_; lean_object* v_res_2664_; 
v___y_172148__boxed_2662_ = lean_unbox(v___y_2655_);
v___x_172149__boxed_2663_ = lean_unbox(v___x_2656_);
v_res_2664_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_172148__boxed_2662_, v___x_172149__boxed_2663_, v_as_x27_2657_, v_b_2658_, v___y_2659_, v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v_as_x27_2657_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object* v_msg_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; lean_object* v___f_2670_; lean_object* v___f_2671_; lean_object* v___f_2672_; lean_object* v___f_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___f_2686_; lean_object* v___x_164180__overap_2687_; lean_object* v___x_2688_; 
v___x_2669_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2670_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2670_, 0, v___x_2669_);
v___f_2671_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2671_, 0, v___x_2669_);
v___f_2672_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2672_, 0, v___x_2669_);
v___f_2673_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2673_, 0, v___x_2669_);
v___x_2674_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2674_, 0, lean_box(0));
lean_closure_set(v___x_2674_, 1, lean_box(0));
lean_closure_set(v___x_2674_, 2, v___x_2669_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
lean_ctor_set(v___x_2675_, 1, v___f_2670_);
v___x_2676_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2676_, 0, lean_box(0));
lean_closure_set(v___x_2676_, 1, lean_box(0));
lean_closure_set(v___x_2676_, 2, v___x_2669_);
v___x_2677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2675_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
lean_ctor_set(v___x_2677_, 2, v___f_2671_);
lean_ctor_set(v___x_2677_, 3, v___f_2672_);
lean_ctor_set(v___x_2677_, 4, v___f_2673_);
v___x_2678_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2678_, 0, lean_box(0));
lean_closure_set(v___x_2678_, 1, lean_box(0));
lean_closure_set(v___x_2678_, 2, v___x_2669_);
v___x_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2681_ = lean_box(1);
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2680_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
v___x_2685_ = l_instInhabitedOfMonad___redArg(v___x_2679_, v___x_2684_);
v___f_2686_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2686_, 0, v___x_2685_);
v___x_164180__overap_2687_ = lean_panic_fn_borrowed(v___f_2686_, v_msg_2665_);
lean_dec_ref(v___f_2686_);
lean_inc_ref(v___y_2666_);
v___x_2688_ = lean_apply_3(v___x_164180__overap_2687_, v___y_2666_, v___y_2667_, lean_box(0));
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object* v_msg_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v_msg_2689_, v___y_2690_, v___y_2691_);
lean_dec_ref(v___y_2690_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object* v_msg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; lean_object* v___f_2699_; lean_object* v___f_2700_; lean_object* v___f_2701_; lean_object* v___f_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___f_2712_; lean_object* v___x_162765__overap_2713_; lean_object* v___x_2714_; 
v___x_2698_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2699_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2699_, 0, v___x_2698_);
v___f_2700_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2700_, 0, v___x_2698_);
v___f_2701_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2701_, 0, v___x_2698_);
v___f_2702_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2702_, 0, v___x_2698_);
v___x_2703_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2703_, 0, lean_box(0));
lean_closure_set(v___x_2703_, 1, lean_box(0));
lean_closure_set(v___x_2703_, 2, v___x_2698_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v___f_2699_);
v___x_2705_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2705_, 0, lean_box(0));
lean_closure_set(v___x_2705_, 1, lean_box(0));
lean_closure_set(v___x_2705_, 2, v___x_2698_);
v___x_2706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
lean_ctor_set(v___x_2706_, 2, v___f_2700_);
lean_ctor_set(v___x_2706_, 3, v___f_2701_);
lean_ctor_set(v___x_2706_, 4, v___f_2702_);
v___x_2707_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2707_, 0, lean_box(0));
lean_closure_set(v___x_2707_, 1, lean_box(0));
lean_closure_set(v___x_2707_, 2, v___x_2698_);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
v___x_2711_ = l_instInhabitedOfMonad___redArg(v___x_2708_, v___x_2710_);
v___f_2712_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2712_, 0, v___x_2711_);
v___x_162765__overap_2713_ = lean_panic_fn_borrowed(v___f_2712_, v_msg_2694_);
lean_dec_ref(v___f_2712_);
lean_inc_ref(v___y_2695_);
v___x_2714_ = lean_apply_3(v___x_162765__overap_2713_, v___y_2695_, v___y_2696_, lean_box(0));
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object* v_msg_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v_msg_2715_, v___y_2716_, v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2719_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2721_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0));
v___x_2722_ = lean_unsigned_to_nat(8u);
v___x_2723_ = lean_unsigned_to_nat(354u);
v___x_2724_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2725_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2726_ = l_mkPanicMessageWithDecl(v___x_2725_, v___x_2724_, v___x_2723_, v___x_2722_, v___x_2721_);
return v___x_2726_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2728_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2));
v___x_2729_ = lean_unsigned_to_nat(13u);
v___x_2730_ = lean_unsigned_to_nat(356u);
v___x_2731_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2732_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2733_ = l_mkPanicMessageWithDecl(v___x_2732_, v___x_2731_, v___x_2730_, v___x_2729_, v___x_2728_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(uint8_t v___x_2734_, lean_object* v_init_2735_, lean_object* v_x_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_d_2741_; lean_object* v___y_2742_; 
if (lean_obj_tag(v_x_2736_) == 0)
{
lean_object* v_k_2746_; lean_object* v_l_2747_; lean_object* v_r_2748_; lean_object* v___x_2749_; 
v_k_2746_ = lean_ctor_get(v_x_2736_, 1);
lean_inc(v_k_2746_);
v_l_2747_ = lean_ctor_get(v_x_2736_, 3);
lean_inc(v_l_2747_);
v_r_2748_ = lean_ctor_get(v_x_2736_, 4);
lean_inc(v_r_2748_);
lean_dec_ref_known(v_x_2736_, 5);
v___x_2749_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_2734_, v_init_2735_, v_l_2747_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v_fst_2751_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v_fst_2751_ = lean_ctor_get(v_a_2750_, 0);
lean_inc(v_fst_2751_);
if (lean_obj_tag(v_fst_2751_) == 0)
{
lean_object* v_snd_2752_; lean_object* v_a_2753_; 
lean_dec(v_r_2748_);
lean_dec(v_k_2746_);
v_snd_2752_ = lean_ctor_get(v_a_2750_, 1);
lean_inc(v_snd_2752_);
lean_dec(v_a_2750_);
v_a_2753_ = lean_ctor_get(v_fst_2751_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v_fst_2751_, 1);
v_d_2741_ = v_a_2753_;
v___y_2742_ = v_snd_2752_;
goto v___jp_2740_;
}
else
{
lean_object* v_snd_2754_; lean_object* v_a_2755_; lean_object* v___y_2757_; lean_object* v___y_2761_; lean_object* v___x_2787_; 
v_snd_2754_ = lean_ctor_get(v_a_2750_, 1);
lean_inc(v_snd_2754_);
lean_dec(v_a_2750_);
v_a_2755_ = lean_ctor_get(v_fst_2751_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v_fst_2751_, 1);
lean_inc_ref(v___y_2737_);
v___x_2787_ = l_Lean_Environment_find_x3f(v___y_2737_, v_k_2746_, v___x_2734_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_2789_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2788_);
v___y_2761_ = v___x_2789_;
goto v___jp_2760_;
}
else
{
lean_object* v_val_2790_; 
v_val_2790_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_val_2790_);
lean_dec_ref_known(v___x_2787_, 1);
v___y_2761_ = v_val_2790_;
goto v___jp_2760_;
}
v___jp_2756_:
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_array_push(v_a_2755_, v___y_2757_);
v_init_2735_ = v___x_2758_;
v_x_2736_ = v_r_2748_;
v___y_2738_ = v_snd_2754_;
goto _start;
}
v___jp_2760_:
{
if (lean_obj_tag(v___y_2761_) == 7)
{
lean_object* v_val_2762_; uint8_t v_isUnsafe_2763_; 
v_val_2762_ = lean_ctor_get(v___y_2761_, 0);
lean_inc_ref(v_val_2762_);
lean_dec_ref_known(v___y_2761_, 1);
v_isUnsafe_2763_ = lean_ctor_get_uint8(v_val_2762_, sizeof(void*)*7 + 1);
if (v_isUnsafe_2763_ == 0)
{
v___y_2757_ = v_val_2762_;
goto v___jp_2756_;
}
else
{
if (v___x_2734_ == 0)
{
uint8_t v_exportUnsafe_2764_; 
v_exportUnsafe_2764_ = lean_ctor_get_uint8(v_snd_2754_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec_ref(v_val_2762_);
lean_dec(v_a_2755_);
v___x_2765_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1);
v___x_2766_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v___x_2765_, v___y_2737_, v_snd_2754_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v_fst_2768_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
v_fst_2768_ = lean_ctor_get(v_a_2767_, 0);
lean_inc(v_fst_2768_);
if (lean_obj_tag(v_fst_2768_) == 0)
{
lean_object* v_snd_2769_; lean_object* v_a_2770_; 
lean_dec(v_r_2748_);
v_snd_2769_ = lean_ctor_get(v_a_2767_, 1);
lean_inc(v_snd_2769_);
lean_dec(v_a_2767_);
v_a_2770_ = lean_ctor_get(v_fst_2768_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v_fst_2768_, 1);
v_d_2741_ = v_a_2770_;
v___y_2742_ = v_snd_2769_;
goto v___jp_2740_;
}
else
{
lean_object* v_snd_2771_; lean_object* v_a_2772_; 
v_snd_2771_ = lean_ctor_get(v_a_2767_, 1);
lean_inc(v_snd_2771_);
lean_dec(v_a_2767_);
v_a_2772_ = lean_ctor_get(v_fst_2768_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v_fst_2768_, 1);
v_init_2735_ = v_a_2772_;
v_x_2736_ = v_r_2748_;
v___y_2738_ = v_snd_2771_;
goto _start;
}
}
else
{
lean_dec(v_r_2748_);
return v___x_2766_;
}
}
else
{
v___y_2757_ = v_val_2762_;
goto v___jp_2756_;
}
}
else
{
v___y_2757_ = v_val_2762_;
goto v___jp_2756_;
}
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_dec_ref(v___y_2761_);
v___x_2774_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3);
v___x_2775_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2774_, v___y_2737_, v_snd_2754_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v_snd_2777_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v_snd_2777_ = lean_ctor_get(v_a_2776_, 1);
lean_inc(v_snd_2777_);
lean_dec(v_a_2776_);
v_init_2735_ = v_a_2755_;
v_x_2736_ = v_r_2748_;
v___y_2738_ = v_snd_2777_;
goto _start;
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_a_2755_);
lean_dec(v_r_2748_);
v_a_2779_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2775_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2775_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
}
}
else
{
lean_dec(v_r_2748_);
lean_dec(v_k_2746_);
return v___x_2749_;
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_init_2735_);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v___y_2738_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
v___jp_2740_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2743_, 0, v_d_2741_);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v___y_2742_);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___boxed(lean_object* v___x_2794_, lean_object* v_init_2795_, lean_object* v_x_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
uint8_t v___x_172445__boxed_2800_; lean_object* v_res_2801_; 
v___x_172445__boxed_2800_ = lean_unbox(v___x_2794_);
v_res_2801_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_172445__boxed_2800_, v_init_2795_, v_x_2796_, v___y_2797_, v___y_2798_);
lean_dec_ref(v___y_2797_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(size_t v_sz_2802_, size_t v_i_2803_, lean_object* v_bs_2804_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = lean_usize_dec_lt(v_i_2803_, v_sz_2802_);
if (v___x_2805_ == 0)
{
return v_bs_2804_;
}
else
{
lean_object* v_v_2806_; lean_object* v___x_2807_; lean_object* v_bs_x27_2808_; size_t v___x_2809_; size_t v___x_2810_; lean_object* v___x_2811_; 
v_v_2806_ = lean_array_uget(v_bs_2804_, v_i_2803_);
v___x_2807_ = lean_unsigned_to_nat(0u);
v_bs_x27_2808_ = lean_array_uset(v_bs_2804_, v_i_2803_, v___x_2807_);
v___x_2809_ = ((size_t)1ULL);
v___x_2810_ = lean_usize_add(v_i_2803_, v___x_2809_);
v___x_2811_ = lean_array_uset(v_bs_x27_2808_, v_i_2803_, v_v_2806_);
v_i_2803_ = v___x_2810_;
v_bs_2804_ = v___x_2811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23___boxed(lean_object* v_sz_2813_, lean_object* v_i_2814_, lean_object* v_bs_2815_){
_start:
{
size_t v_sz_boxed_2816_; size_t v_i_boxed_2817_; lean_object* v_res_2818_; 
v_sz_boxed_2816_ = lean_unbox_usize(v_sz_2813_);
lean_dec(v_sz_2813_);
v_i_boxed_2817_ = lean_unbox_usize(v_i_2814_);
lean_dec(v_i_2814_);
v_res_2818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(v_sz_boxed_2816_, v_i_boxed_2817_, v_bs_2815_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(lean_object* v_a_2819_){
_start:
{
size_t v_sz_2820_; size_t v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_sz_2820_ = lean_array_size(v_a_2819_);
v___x_2821_ = ((size_t)0ULL);
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(v_sz_2820_, v___x_2821_, v_a_2819_);
v___x_2823_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object* v_a_2824_){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_array_mk(v_a_2824_);
v___x_2826_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object* v_as_2827_, size_t v_sz_2828_, size_t v_i_2829_, lean_object* v_b_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
uint8_t v___x_2834_; 
v___x_2834_ = lean_usize_dec_lt(v_i_2829_, v_sz_2828_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2835_, 0, v_b_2830_);
lean_ctor_set(v___x_2835_, 1, v___y_2832_);
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
return v___x_2836_;
}
else
{
lean_object* v_visitedNames_2837_; lean_object* v_visitedLevels_2838_; lean_object* v_visitedExprs_2839_; lean_object* v_visitedConstants_2840_; lean_object* v_noMDataExprs_2841_; uint8_t v_exportMData_2842_; uint8_t v_exportUnsafe_2843_; uint8_t v_ignoreMissing_2844_; lean_object* v_recursorMap_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2864_; 
v_visitedNames_2837_ = lean_ctor_get(v___y_2832_, 0);
v_visitedLevels_2838_ = lean_ctor_get(v___y_2832_, 1);
v_visitedExprs_2839_ = lean_ctor_get(v___y_2832_, 2);
v_visitedConstants_2840_ = lean_ctor_get(v___y_2832_, 3);
v_noMDataExprs_2841_ = lean_ctor_get(v___y_2832_, 4);
v_exportMData_2842_ = lean_ctor_get_uint8(v___y_2832_, sizeof(void*)*6);
v_exportUnsafe_2843_ = lean_ctor_get_uint8(v___y_2832_, sizeof(void*)*6 + 1);
v_ignoreMissing_2844_ = lean_ctor_get_uint8(v___y_2832_, sizeof(void*)*6 + 2);
v_recursorMap_2845_ = lean_ctor_get(v___y_2832_, 5);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___y_2832_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2847_ = v___y_2832_;
v_isShared_2848_ = v_isSharedCheck_2864_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_recursorMap_2845_);
lean_inc(v_noMDataExprs_2841_);
lean_inc(v_visitedConstants_2840_);
lean_inc(v_visitedExprs_2839_);
lean_inc(v_visitedLevels_2838_);
lean_inc(v_visitedNames_2837_);
lean_dec(v___y_2832_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2864_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v_a_2849_; lean_object* v_toConstantVal_2850_; lean_object* v_name_2851_; lean_object* v_type_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v_a_2849_ = lean_array_uget_borrowed(v_as_2827_, v_i_2829_);
v_toConstantVal_2850_ = lean_ctor_get(v_a_2849_, 0);
v_name_2851_ = lean_ctor_get(v_toConstantVal_2850_, 0);
v_type_2852_ = lean_ctor_get(v_toConstantVal_2850_, 2);
v___x_2853_ = lean_box(0);
lean_inc(v_name_2851_);
v___x_2854_ = l_Lean_NameHashSet_insert(v_visitedConstants_2840_, v_name_2851_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 3, v___x_2854_);
v___x_2856_ = v___x_2847_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_visitedNames_2837_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_visitedLevels_2838_);
lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_visitedExprs_2839_);
lean_ctor_set(v_reuseFailAlloc_2863_, 3, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2863_, 4, v_noMDataExprs_2841_);
lean_ctor_set(v_reuseFailAlloc_2863_, 5, v_recursorMap_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, sizeof(void*)*6, v_exportMData_2842_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, sizeof(void*)*6 + 1, v_exportUnsafe_2843_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, sizeof(void*)*6 + 2, v_ignoreMissing_2844_);
v___x_2856_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2857_; 
lean_inc_ref(v_type_2852_);
v___x_2857_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_2852_, v___y_2831_, v___x_2856_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v_snd_2859_; size_t v___x_2860_; size_t v___x_2861_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v_snd_2859_ = lean_ctor_get(v_a_2858_, 1);
lean_inc(v_snd_2859_);
lean_dec(v_a_2858_);
v___x_2860_ = ((size_t)1ULL);
v___x_2861_ = lean_usize_add(v_i_2829_, v___x_2860_);
v_i_2829_ = v___x_2861_;
v_b_2830_ = v___x_2853_;
v___y_2832_ = v_snd_2859_;
goto _start;
}
else
{
return v___x_2857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object* v_as_x27_2865_, lean_object* v_b_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
if (lean_obj_tag(v_as_x27_2865_) == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v_b_2866_);
lean_ctor_set(v___x_2870_, 1, v___y_2868_);
v___x_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
return v___x_2871_;
}
else
{
lean_object* v_head_2872_; lean_object* v_tail_2873_; lean_object* v_rhs_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_head_2872_ = lean_ctor_get(v_as_x27_2865_, 0);
v_tail_2873_ = lean_ctor_get(v_as_x27_2865_, 1);
v_rhs_2874_ = lean_ctor_get(v_head_2872_, 2);
v___x_2875_ = lean_box(0);
lean_inc_ref(v_rhs_2874_);
v___x_2876_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_rhs_2874_, v___y_2867_, v___y_2868_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v_snd_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
v_snd_2878_ = lean_ctor_get(v_a_2877_, 1);
lean_inc(v_snd_2878_);
lean_dec(v_a_2877_);
v_as_x27_2865_ = v_tail_2873_;
v_b_2866_ = v___x_2875_;
v___y_2868_ = v_snd_2878_;
goto _start;
}
else
{
return v___x_2876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(lean_object* v_as_2880_, size_t v_sz_2881_, size_t v_i_2882_, lean_object* v_b_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v___x_2887_; 
v___x_2887_ = lean_usize_dec_lt(v_i_2882_, v_sz_2881_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v_b_2883_);
lean_ctor_set(v___x_2888_, 1, v___y_2885_);
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
return v___x_2889_;
}
else
{
lean_object* v_a_2890_; lean_object* v_rules_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_a_2890_ = lean_array_uget_borrowed(v_as_2880_, v_i_2882_);
v_rules_2891_ = lean_ctor_get(v_a_2890_, 6);
v___x_2892_ = lean_box(0);
v___x_2893_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_rules_2891_, v___x_2892_, v___y_2884_, v___y_2885_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v_snd_2895_; size_t v___x_2896_; size_t v___x_2897_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v_snd_2895_ = lean_ctor_get(v_a_2894_, 1);
lean_inc(v_snd_2895_);
lean_dec(v_a_2894_);
v___x_2896_ = ((size_t)1ULL);
v___x_2897_ = lean_usize_add(v_i_2882_, v___x_2896_);
v_i_2882_ = v___x_2897_;
v_b_2883_ = v___x_2892_;
v___y_2885_ = v_snd_2895_;
goto _start;
}
else
{
return v___x_2893_;
}
}
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__0(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = lean_box(0);
v___x_2900_ = lean_unsigned_to_nat(16u);
v___x_2901_ = lean_mk_array(v___x_2900_, v___x_2899_);
return v___x_2901_;
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__1(void){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2902_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__0, &l_LeanExport_dumpExpr___closed__0_once, _init_l_LeanExport_dumpExpr___closed__0);
v___x_2903_ = lean_unsigned_to_nat(0u);
v___x_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
lean_ctor_set(v___x_2904_, 1, v___x_2902_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v_visitedConstants_2931_; lean_object* v_nat_2932_; uint8_t v___x_2933_; 
v_visitedConstants_2931_ = lean_ctor_get(v_a_2925_, 3);
v_nat_2932_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1));
v___x_2933_ = l_Lean_NameHashSet_contains(v_visitedConstants_2931_, v_nat_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; 
lean_inc_ref(v_a_2924_);
v___x_2934_ = l_Lean_Environment_find_x3f(v_a_2924_, v_nat_2932_, v___x_2933_);
if (lean_obj_tag(v___x_2934_) == 0)
{
goto v___jp_2927_;
}
else
{
lean_object* v___x_2935_; 
lean_dec_ref_known(v___x_2934_, 1);
v___x_2935_ = l_LeanExport_dumpConstant(v_nat_2932_, v_a_2924_, v_a_2925_);
return v___x_2935_;
}
}
else
{
goto v___jp_2927_;
}
v___jp_2927_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
lean_ctor_set(v___x_2929_, 1, v_a_2925_);
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___y_2951_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v_visitedConstants_2958_; lean_object* v_visitedConstants_2963_; lean_object* v_charOfNat_2964_; uint8_t v___x_2965_; 
v_visitedConstants_2963_ = lean_ctor_get(v_a_2948_, 3);
v_charOfNat_2964_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5));
v___x_2965_ = l_Lean_NameHashSet_contains(v_visitedConstants_2963_, v_charOfNat_2964_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; 
lean_inc_ref(v_a_2947_);
v___x_2966_ = l_Lean_Environment_find_x3f(v_a_2947_, v_charOfNat_2964_, v___x_2965_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_inc_ref(v_visitedConstants_2963_);
v___y_2956_ = v_a_2947_;
v___y_2957_ = v_a_2948_;
v_visitedConstants_2958_ = v_visitedConstants_2963_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2967_; 
lean_dec_ref_known(v___x_2966_, 1);
v___x_2967_ = l_LeanExport_dumpConstant(v_charOfNat_2964_, v_a_2947_, v_a_2948_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v_snd_2969_; lean_object* v_visitedConstants_2970_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v_snd_2969_ = lean_ctor_get(v_a_2968_, 1);
lean_inc(v_snd_2969_);
lean_dec(v_a_2968_);
v_visitedConstants_2970_ = lean_ctor_get(v_snd_2969_, 3);
lean_inc_ref(v_visitedConstants_2970_);
v___y_2956_ = v_a_2947_;
v___y_2957_ = v_snd_2969_;
v_visitedConstants_2958_ = v_visitedConstants_2970_;
goto v___jp_2955_;
}
else
{
return v___x_2967_;
}
}
}
else
{
lean_inc_ref(v_visitedConstants_2963_);
v___y_2956_ = v_a_2947_;
v___y_2957_ = v_a_2948_;
v_visitedConstants_2958_ = v_visitedConstants_2963_;
goto v___jp_2955_;
}
v___jp_2950_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = lean_box(0);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v___y_2951_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
v___jp_2955_:
{
lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2959_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2));
v___x_2960_ = l_Lean_NameHashSet_contains(v_visitedConstants_2958_, v___x_2959_);
lean_dec_ref(v_visitedConstants_2958_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
lean_inc_ref(v___y_2956_);
v___x_2961_ = l_Lean_Environment_find_x3f(v___y_2956_, v___x_2959_, v___x_2960_);
if (lean_obj_tag(v___x_2961_) == 0)
{
v___y_2951_ = v___y_2957_;
goto v___jp_2950_;
}
else
{
lean_object* v___x_2962_; 
lean_dec_ref_known(v___x_2961_, 1);
v___x_2962_ = l_LeanExport_dumpConstant(v___x_2959_, v___y_2956_, v___y_2957_);
return v___x_2962_;
}
}
else
{
v___y_2951_ = v___y_2957_;
goto v___jp_2950_;
}
}
}
}
static lean_object* _init_l_LeanExport_dumpExprAux___closed__26(void){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2981_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__25));
v___x_2982_ = lean_unsigned_to_nat(29u);
v___x_2983_ = lean_unsigned_to_nat(177u);
v___x_2984_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__24));
v___x_2985_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2986_ = l_mkPanicMessageWithDecl(v___x_2985_, v___x_2984_, v___x_2983_, v___x_2982_, v___x_2981_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux(lean_object* v_e_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_visitedNames_2991_; lean_object* v_visitedLevels_2992_; lean_object* v_visitedExprs_2993_; lean_object* v_visitedConstants_2994_; lean_object* v_noMDataExprs_2995_; uint8_t v_exportMData_2996_; uint8_t v_exportUnsafe_2997_; uint8_t v_ignoreMissing_2998_; lean_object* v_recursorMap_2999_; lean_object* v___x_3000_; 
v_visitedNames_2991_ = lean_ctor_get(v_a_2989_, 0);
v_visitedLevels_2992_ = lean_ctor_get(v_a_2989_, 1);
v_visitedExprs_2993_ = lean_ctor_get(v_a_2989_, 2);
v_visitedConstants_2994_ = lean_ctor_get(v_a_2989_, 3);
v_noMDataExprs_2995_ = lean_ctor_get(v_a_2989_, 4);
v_exportMData_2996_ = lean_ctor_get_uint8(v_a_2989_, sizeof(void*)*6);
v_exportUnsafe_2997_ = lean_ctor_get_uint8(v_a_2989_, sizeof(void*)*6 + 1);
v_ignoreMissing_2998_ = lean_ctor_get_uint8(v_a_2989_, sizeof(void*)*6 + 2);
v_recursorMap_2999_ = lean_ctor_get(v_a_2989_, 5);
v___x_3000_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_visitedExprs_2993_, v_e_2987_);
if (lean_obj_tag(v___x_3000_) == 1)
{
lean_object* v_val_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3009_; 
lean_dec_ref(v_e_2987_);
v_val_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3009_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_val_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3009_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v_val_3001_);
lean_ctor_set(v___x_3005_, 1, v_a_2989_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set_tag(v___x_3003_, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3005_);
v___x_3007_ = v___x_3003_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
else
{
lean_object* v___x_3010_; lean_object* v_fst_3012_; lean_object* v_visitedNames_3013_; lean_object* v_visitedLevels_3014_; lean_object* v_visitedExprs_3015_; lean_object* v_visitedConstants_3016_; lean_object* v_noMDataExprs_3017_; uint8_t v_exportMData_3018_; uint8_t v_exportUnsafe_3019_; uint8_t v_ignoreMissing_3020_; lean_object* v_recursorMap_3021_; lean_object* v_fst_3048_; lean_object* v_snd_3049_; 
lean_dec(v___x_3000_);
v___x_3010_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__0));
switch(lean_obj_tag(v_e_2987_))
{
case 0:
{
lean_object* v_deBruijnIndex_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_inc(v_recursorMap_2999_);
lean_inc_ref(v_noMDataExprs_2995_);
lean_inc_ref(v_visitedConstants_2994_);
lean_inc_ref(v_visitedExprs_2993_);
lean_inc_ref(v_visitedLevels_2992_);
lean_inc_ref(v_visitedNames_2991_);
lean_dec_ref(v_a_2989_);
v_deBruijnIndex_3059_ = lean_ctor_get(v_e_2987_, 0);
v___x_3060_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__1));
lean_inc(v_deBruijnIndex_3059_);
v___x_3061_ = l_Lean_JsonNumber_fromNat(v_deBruijnIndex_3059_);
v___x_3062_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3060_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = l_Lean_Json_mkObj(v___x_3065_);
lean_dec_ref_known(v___x_3065_, 2);
v_fst_3012_ = v___x_3066_;
v_visitedNames_3013_ = v_visitedNames_2991_;
v_visitedLevels_3014_ = v_visitedLevels_2992_;
v_visitedExprs_3015_ = v_visitedExprs_2993_;
v_visitedConstants_3016_ = v_visitedConstants_2994_;
v_noMDataExprs_3017_ = v_noMDataExprs_2995_;
v_exportMData_3018_ = v_exportMData_2996_;
v_exportUnsafe_3019_ = v_exportUnsafe_2997_;
v_ignoreMissing_3020_ = v_ignoreMissing_2998_;
v_recursorMap_3021_ = v_recursorMap_2999_;
goto v___jp_3011_;
}
case 3:
{
lean_object* v_u_3067_; lean_object* v___x_3068_; 
v_u_3067_ = lean_ctor_get(v_e_2987_, 0);
lean_inc(v_u_3067_);
v___x_3068_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_u_3067_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3090_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3090_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3090_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v_fst_3073_; lean_object* v_snd_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3089_; 
v_fst_3073_ = lean_ctor_get(v_a_3069_, 0);
v_snd_3074_ = lean_ctor_get(v_a_3069_, 1);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_a_3069_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3076_ = v_a_3069_;
v_isShared_3077_ = v_isSharedCheck_3089_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_snd_3074_);
lean_inc(v_fst_3073_);
lean_dec(v_a_3069_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3089_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3078_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__2));
v___x_3079_ = l_Lean_JsonNumber_fromNat(v_fst_3073_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set_tag(v___x_3071_, 2);
lean_ctor_set(v___x_3071_, 0, v___x_3079_);
v___x_3081_ = v___x_3071_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3083_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 1, v___x_3081_);
lean_ctor_set(v___x_3076_, 0, v___x_3078_);
v___x_3083_ = v___x_3076_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v___x_3081_);
v___x_3083_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3083_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___x_3086_ = l_Lean_Json_mkObj(v___x_3085_);
lean_dec_ref_known(v___x_3085_, 2);
v_fst_3048_ = v___x_3086_;
v_snd_3049_ = v_snd_3074_;
goto v___jp_3047_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2987_, 1);
return v___x_3068_;
}
}
case 4:
{
lean_object* v_declName_3091_; lean_object* v_us_3092_; lean_object* v___x_3093_; 
v_declName_3091_ = lean_ctor_get(v_e_2987_, 0);
v_us_3092_ = lean_ctor_get(v_e_2987_, 1);
lean_inc(v_declName_3091_);
v___x_3093_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3091_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3141_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3141_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3141_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_fst_3098_; lean_object* v_snd_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3140_; 
v_fst_3098_ = lean_ctor_get(v_a_3094_, 0);
v_snd_3099_ = lean_ctor_get(v_a_3094_, 1);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_a_3094_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3101_ = v_a_3094_;
v_isShared_3102_ = v_isSharedCheck_3140_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_snd_3099_);
lean_inc(v_fst_3098_);
lean_dec(v_a_3094_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3140_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = lean_box(0);
lean_inc(v_us_3092_);
v___x_3104_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_us_3092_, v___x_3103_, v_a_2988_, v_snd_3099_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v_fst_3106_; lean_object* v_snd_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3131_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
v_fst_3106_ = lean_ctor_get(v_a_3105_, 0);
v_snd_3107_ = lean_ctor_get(v_a_3105_, 1);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_a_3105_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3109_ = v_a_3105_;
v_isShared_3110_ = v_isSharedCheck_3131_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_snd_3107_);
lean_inc(v_fst_3106_);
lean_dec(v_a_3105_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3131_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3111_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__3));
v___x_3112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3113_ = l_Lean_JsonNumber_fromNat(v_fst_3098_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set_tag(v___x_3096_, 2);
lean_ctor_set(v___x_3096_, 0, v___x_3113_);
v___x_3115_ = v___x_3096_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3117_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v___x_3115_);
lean_ctor_set(v___x_3109_, 0, v___x_3112_);
v___x_3117_ = v___x_3109_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3118_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__4));
v___x_3119_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_3106_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 1, v___x_3119_);
lean_ctor_set(v___x_3101_, 0, v___x_3118_);
v___x_3121_ = v___x_3101_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
lean_ctor_set(v___x_3122_, 1, v___x_3103_);
v___x_3123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3117_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_Json_mkObj(v___x_3123_);
lean_dec_ref_known(v___x_3123_, 2);
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3111_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___x_3103_);
v___x_3127_ = l_Lean_Json_mkObj(v___x_3126_);
lean_dec_ref_known(v___x_3126_, 2);
v_fst_3048_ = v___x_3127_;
v_snd_3049_ = v_snd_3107_;
goto v___jp_3047_;
}
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_del_object(v___x_3101_);
lean_dec(v_fst_3098_);
lean_del_object(v___x_3096_);
lean_dec_ref_known(v_e_2987_, 2);
v_a_3132_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3104_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3104_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2987_, 2);
return v___x_3093_;
}
}
case 5:
{
lean_object* v_fn_3142_; lean_object* v_arg_3143_; lean_object* v___x_3144_; 
v_fn_3142_ = lean_ctor_get(v_e_2987_, 0);
v_arg_3143_ = lean_ctor_get(v_e_2987_, 1);
lean_inc_ref(v_fn_3142_);
v___x_3144_ = l_LeanExport_dumpExprAux(v_fn_3142_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3191_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3191_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3191_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v_fst_3149_; lean_object* v_snd_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3190_; 
v_fst_3149_ = lean_ctor_get(v_a_3145_, 0);
v_snd_3150_ = lean_ctor_get(v_a_3145_, 1);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_a_3145_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3152_ = v_a_3145_;
v_isShared_3153_ = v_isSharedCheck_3190_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_snd_3150_);
lean_inc(v_fst_3149_);
lean_dec(v_a_3145_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3190_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3154_; 
lean_inc_ref(v_arg_3143_);
v___x_3154_ = l_LeanExport_dumpExprAux(v_arg_3143_, v_a_2988_, v_snd_3150_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3189_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3157_ = v___x_3154_;
v_isShared_3158_ = v_isSharedCheck_3189_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3189_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v_fst_3159_; lean_object* v_snd_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3188_; 
v_fst_3159_ = lean_ctor_get(v_a_3155_, 0);
v_snd_3160_ = lean_ctor_get(v_a_3155_, 1);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_a_3155_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3162_ = v_a_3155_;
v_isShared_3163_ = v_isSharedCheck_3188_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_snd_3160_);
lean_inc(v_fst_3159_);
lean_dec(v_a_3155_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3188_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3164_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__5));
v___x_3165_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__6));
v___x_3166_ = l_Lean_JsonNumber_fromNat(v_fst_3149_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set_tag(v___x_3157_, 2);
lean_ctor_set(v___x_3157_, 0, v___x_3166_);
v___x_3168_ = v___x_3157_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3170_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3168_);
lean_ctor_set(v___x_3162_, 0, v___x_3165_);
v___x_3170_ = v___x_3162_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3171_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__7));
v___x_3172_ = l_Lean_JsonNumber_fromNat(v_fst_3159_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 2);
lean_ctor_set(v___x_3147_, 0, v___x_3172_);
v___x_3174_ = v___x_3147_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3172_);
v___x_3174_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
lean_object* v___x_3176_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 1, v___x_3174_);
lean_ctor_set(v___x_3152_, 0, v___x_3171_);
v___x_3176_ = v___x_3152_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3176_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3170_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = l_Lean_Json_mkObj(v___x_3179_);
lean_dec_ref_known(v___x_3179_, 2);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3164_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v___x_3177_);
v___x_3183_ = l_Lean_Json_mkObj(v___x_3182_);
lean_dec_ref_known(v___x_3182_, 2);
v_fst_3048_ = v___x_3183_;
v_snd_3049_ = v_snd_3160_;
goto v___jp_3047_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3152_);
lean_dec(v_fst_3149_);
lean_del_object(v___x_3147_);
lean_dec_ref_known(v_e_2987_, 2);
return v___x_3154_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2987_, 2);
return v___x_3144_;
}
}
case 6:
{
lean_object* v_binderName_3192_; lean_object* v_binderType_3193_; lean_object* v_body_3194_; uint8_t v_binderInfo_3195_; lean_object* v___x_3196_; 
v_binderName_3192_ = lean_ctor_get(v_e_2987_, 0);
v_binderType_3193_ = lean_ctor_get(v_e_2987_, 1);
v_body_3194_ = lean_ctor_get(v_e_2987_, 2);
v_binderInfo_3195_ = lean_ctor_get_uint8(v_e_2987_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3192_);
v___x_3196_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3192_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3268_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3268_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3268_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v_fst_3201_; lean_object* v_snd_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3267_; 
v_fst_3201_ = lean_ctor_get(v_a_3197_, 0);
v_snd_3202_ = lean_ctor_get(v_a_3197_, 1);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_a_3197_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3204_ = v_a_3197_;
v_isShared_3205_ = v_isSharedCheck_3267_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_snd_3202_);
lean_inc(v_fst_3201_);
lean_dec(v_a_3197_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3267_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; 
lean_inc_ref(v_binderType_3193_);
v___x_3206_ = l_LeanExport_dumpExprAux(v_binderType_3193_, v_a_2988_, v_snd_3202_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3266_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3209_ = v___x_3206_;
v_isShared_3210_ = v_isSharedCheck_3266_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3266_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v_fst_3211_; lean_object* v_snd_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3265_; 
v_fst_3211_ = lean_ctor_get(v_a_3207_, 0);
v_snd_3212_ = lean_ctor_get(v_a_3207_, 1);
v_isSharedCheck_3265_ = !lean_is_exclusive(v_a_3207_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3214_ = v_a_3207_;
v_isShared_3215_ = v_isSharedCheck_3265_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_snd_3212_);
lean_inc(v_fst_3211_);
lean_dec(v_a_3207_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3265_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; 
lean_inc_ref(v_body_3194_);
v___x_3216_ = l_LeanExport_dumpExprAux(v_body_3194_, v_a_2988_, v_snd_3212_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3264_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3219_ = v___x_3216_;
v_isShared_3220_ = v_isSharedCheck_3264_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3264_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_fst_3221_; lean_object* v_snd_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3263_; 
v_fst_3221_ = lean_ctor_get(v_a_3217_, 0);
v_snd_3222_ = lean_ctor_get(v_a_3217_, 1);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_a_3217_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3224_ = v_a_3217_;
v_isShared_3225_ = v_isSharedCheck_3263_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_snd_3222_);
lean_inc(v_fst_3221_);
lean_dec(v_a_3217_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3263_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3226_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__8));
v___x_3227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3228_ = l_Lean_JsonNumber_fromNat(v_fst_3201_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set_tag(v___x_3219_, 2);
lean_ctor_set(v___x_3219_, 0, v___x_3228_);
v___x_3230_ = v___x_3219_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3232_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 1, v___x_3230_);
lean_ctor_set(v___x_3224_, 0, v___x_3227_);
v___x_3232_ = v___x_3224_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3227_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3233_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3234_ = l_Lean_JsonNumber_fromNat(v_fst_3211_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 2);
lean_ctor_set(v___x_3209_, 0, v___x_3234_);
v___x_3236_ = v___x_3209_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3238_; 
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 1, v___x_3236_);
lean_ctor_set(v___x_3214_, 0, v___x_3233_);
v___x_3238_ = v___x_3214_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3239_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3240_ = l_Lean_JsonNumber_fromNat(v_fst_3221_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 2);
lean_ctor_set(v___x_3199_, 0, v___x_3240_);
v___x_3242_ = v___x_3199_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___x_3242_);
lean_ctor_set(v___x_3204_, 0, v___x_3239_);
v___x_3244_ = v___x_3204_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3245_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3246_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3195_);
v___x_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_box(0);
v___x_3249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3244_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3238_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3232_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = l_Lean_Json_mkObj(v___x_3252_);
lean_dec_ref_known(v___x_3252_, 2);
v___x_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3226_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v___x_3248_);
v___x_3256_ = l_Lean_Json_mkObj(v___x_3255_);
lean_dec_ref_known(v___x_3255_, 2);
v_fst_3048_ = v___x_3256_;
v_snd_3049_ = v_snd_3222_;
goto v___jp_3047_;
}
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
lean_del_object(v___x_3214_);
lean_dec(v_fst_3211_);
lean_del_object(v___x_3209_);
lean_del_object(v___x_3204_);
lean_dec(v_fst_3201_);
lean_del_object(v___x_3199_);
lean_dec_ref_known(v_e_2987_, 3);
return v___x_3216_;
}
}
}
}
else
{
lean_del_object(v___x_3204_);
lean_dec(v_fst_3201_);
lean_del_object(v___x_3199_);
lean_dec_ref_known(v_e_2987_, 3);
return v___x_3206_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2987_, 3);
return v___x_3196_;
}
}
case 7:
{
lean_object* v_binderName_3269_; lean_object* v_binderType_3270_; lean_object* v_body_3271_; uint8_t v_binderInfo_3272_; lean_object* v___x_3273_; 
v_binderName_3269_ = lean_ctor_get(v_e_2987_, 0);
v_binderType_3270_ = lean_ctor_get(v_e_2987_, 1);
v_body_3271_ = lean_ctor_get(v_e_2987_, 2);
v_binderInfo_3272_ = lean_ctor_get_uint8(v_e_2987_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3269_);
v___x_3273_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3269_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3345_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3276_ = v___x_3273_;
v_isShared_3277_ = v_isSharedCheck_3345_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3273_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3345_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v_fst_3278_; lean_object* v_snd_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3344_; 
v_fst_3278_ = lean_ctor_get(v_a_3274_, 0);
v_snd_3279_ = lean_ctor_get(v_a_3274_, 1);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_a_3274_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3281_ = v_a_3274_;
v_isShared_3282_ = v_isSharedCheck_3344_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_snd_3279_);
lean_inc(v_fst_3278_);
lean_dec(v_a_3274_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3344_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3283_; 
lean_inc_ref(v_binderType_3270_);
v___x_3283_ = l_LeanExport_dumpExprAux(v_binderType_3270_, v_a_2988_, v_snd_3279_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3343_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3286_ = v___x_3283_;
v_isShared_3287_ = v_isSharedCheck_3343_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3343_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_fst_3288_; lean_object* v_snd_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3342_; 
v_fst_3288_ = lean_ctor_get(v_a_3284_, 0);
v_snd_3289_ = lean_ctor_get(v_a_3284_, 1);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_a_3284_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3291_ = v_a_3284_;
v_isShared_3292_ = v_isSharedCheck_3342_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_snd_3289_);
lean_inc(v_fst_3288_);
lean_dec(v_a_3284_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3342_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; 
lean_inc_ref(v_body_3271_);
v___x_3293_ = l_LeanExport_dumpExprAux(v_body_3271_, v_a_2988_, v_snd_3289_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3341_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3296_ = v___x_3293_;
v_isShared_3297_ = v_isSharedCheck_3341_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3293_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3341_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v_fst_3298_; lean_object* v_snd_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3340_; 
v_fst_3298_ = lean_ctor_get(v_a_3294_, 0);
v_snd_3299_ = lean_ctor_get(v_a_3294_, 1);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_a_3294_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3301_ = v_a_3294_;
v_isShared_3302_ = v_isSharedCheck_3340_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_snd_3299_);
lean_inc(v_fst_3298_);
lean_dec(v_a_3294_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3340_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3307_; 
v___x_3303_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__11));
v___x_3304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3305_ = l_Lean_JsonNumber_fromNat(v_fst_3278_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set_tag(v___x_3296_, 2);
lean_ctor_set(v___x_3296_, 0, v___x_3305_);
v___x_3307_ = v___x_3296_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3305_);
v___x_3307_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3309_; 
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 1, v___x_3307_);
lean_ctor_set(v___x_3301_, 0, v___x_3304_);
v___x_3309_ = v___x_3301_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3304_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3310_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3311_ = l_Lean_JsonNumber_fromNat(v_fst_3288_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set_tag(v___x_3286_, 2);
lean_ctor_set(v___x_3286_, 0, v___x_3311_);
v___x_3313_ = v___x_3286_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3315_; 
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v___x_3313_);
lean_ctor_set(v___x_3291_, 0, v___x_3310_);
v___x_3315_ = v___x_3291_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3316_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3317_ = l_Lean_JsonNumber_fromNat(v_fst_3298_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set_tag(v___x_3276_, 2);
lean_ctor_set(v___x_3276_, 0, v___x_3317_);
v___x_3319_ = v___x_3276_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3321_; 
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 1, v___x_3319_);
lean_ctor_set(v___x_3281_, 0, v___x_3316_);
v___x_3321_ = v___x_3281_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v___x_3319_);
v___x_3321_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3322_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3323_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3272_);
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = lean_box(0);
v___x_3326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3324_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3321_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3315_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3309_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = l_Lean_Json_mkObj(v___x_3329_);
lean_dec_ref_known(v___x_3329_, 2);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3303_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___x_3332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
lean_ctor_set(v___x_3332_, 1, v___x_3325_);
v___x_3333_ = l_Lean_Json_mkObj(v___x_3332_);
lean_dec_ref_known(v___x_3332_, 2);
v_fst_3048_ = v___x_3333_;
v_snd_3049_ = v_snd_3299_;
goto v___jp_3047_;
}
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
lean_del_object(v___x_3291_);
lean_dec(v_fst_3288_);
lean_del_object(v___x_3286_);
lean_del_object(v___x_3281_);
lean_dec(v_fst_3278_);
lean_del_object(v___x_3276_);
lean_dec_ref_known(v_e_2987_, 3);
return v___x_3293_;
}
}
}
}
else
{
lean_del_object(v___x_3281_);
lean_dec(v_fst_3278_);
lean_del_object(v___x_3276_);
lean_dec_ref_known(v_e_2987_, 3);
return v___x_3283_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2987_, 3);
return v___x_3273_;
}
}
case 8:
{
lean_object* v_declName_3346_; lean_object* v_type_3347_; lean_object* v_value_3348_; lean_object* v_body_3349_; uint8_t v_nondep_3350_; lean_object* v___x_3351_; 
v_declName_3346_ = lean_ctor_get(v_e_2987_, 0);
v_type_3347_ = lean_ctor_get(v_e_2987_, 1);
v_value_3348_ = lean_ctor_get(v_e_2987_, 2);
v_body_3349_ = lean_ctor_get(v_e_2987_, 3);
v_nondep_3350_ = lean_ctor_get_uint8(v_e_2987_, sizeof(void*)*4 + 8);
lean_inc(v_declName_3346_);
v___x_3351_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3346_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3444_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3444_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3444_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v_fst_3356_; lean_object* v_snd_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3443_; 
v_fst_3356_ = lean_ctor_get(v_a_3352_, 0);
v_snd_3357_ = lean_ctor_get(v_a_3352_, 1);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_a_3352_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3359_ = v_a_3352_;
v_isShared_3360_ = v_isSharedCheck_3443_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_snd_3357_);
lean_inc(v_fst_3356_);
lean_dec(v_a_3352_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3443_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; 
lean_inc_ref(v_type_3347_);
v___x_3361_ = l_LeanExport_dumpExprAux(v_type_3347_, v_a_2988_, v_snd_3357_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3442_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3442_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3442_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_fst_3366_; lean_object* v_snd_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3441_; 
v_fst_3366_ = lean_ctor_get(v_a_3362_, 0);
v_snd_3367_ = lean_ctor_get(v_a_3362_, 1);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_a_3362_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3369_ = v_a_3362_;
v_isShared_3370_ = v_isSharedCheck_3441_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_snd_3367_);
lean_inc(v_fst_3366_);
lean_dec(v_a_3362_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3441_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; 
lean_inc_ref(v_value_3348_);
v___x_3371_ = l_LeanExport_dumpExprAux(v_value_3348_, v_a_2988_, v_snd_3367_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3440_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3440_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3440_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v_fst_3376_; lean_object* v_snd_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3439_; 
v_fst_3376_ = lean_ctor_get(v_a_3372_, 0);
v_snd_3377_ = lean_ctor_get(v_a_3372_, 1);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_a_3372_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3379_ = v_a_3372_;
v_isShared_3380_ = v_isSharedCheck_3439_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_snd_3377_);
lean_inc(v_fst_3376_);
lean_dec(v_a_3372_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3439_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; 
lean_inc_ref(v_body_3349_);
v___x_3381_ = l_LeanExport_dumpExprAux(v_body_3349_, v_a_2988_, v_snd_3377_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3438_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3438_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3438_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_fst_3386_; lean_object* v_snd_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3437_; 
v_fst_3386_ = lean_ctor_get(v_a_3382_, 0);
v_snd_3387_ = lean_ctor_get(v_a_3382_, 1);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_a_3382_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3389_ = v_a_3382_;
v_isShared_3390_ = v_isSharedCheck_3437_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_snd_3387_);
lean_inc(v_fst_3386_);
lean_dec(v_a_3382_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3437_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3395_; 
v___x_3391_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__12));
v___x_3392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3393_ = l_Lean_JsonNumber_fromNat(v_fst_3356_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set_tag(v___x_3384_, 2);
lean_ctor_set(v___x_3384_, 0, v___x_3393_);
v___x_3395_ = v___x_3384_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
lean_object* v___x_3397_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 1, v___x_3395_);
lean_ctor_set(v___x_3389_, 0, v___x_3392_);
v___x_3397_ = v___x_3389_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3435_, 1, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3398_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3399_ = l_Lean_JsonNumber_fromNat(v_fst_3366_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 2);
lean_ctor_set(v___x_3374_, 0, v___x_3399_);
v___x_3401_ = v___x_3374_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3403_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 1, v___x_3401_);
lean_ctor_set(v___x_3379_, 0, v___x_3398_);
v___x_3403_ = v___x_3379_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3404_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_3405_ = l_Lean_JsonNumber_fromNat(v_fst_3376_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 2);
lean_ctor_set(v___x_3364_, 0, v___x_3405_);
v___x_3407_ = v___x_3364_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3409_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v___x_3407_);
lean_ctor_set(v___x_3369_, 0, v___x_3404_);
v___x_3409_ = v___x_3369_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3404_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3413_; 
v___x_3410_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3411_ = l_Lean_JsonNumber_fromNat(v_fst_3386_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set_tag(v___x_3354_, 2);
lean_ctor_set(v___x_3354_, 0, v___x_3411_);
v___x_3413_ = v___x_3354_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3415_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v___x_3413_);
lean_ctor_set(v___x_3359_, 0, v___x_3410_);
v___x_3415_ = v___x_3359_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3416_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__14));
v___x_3417_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3417_, 0, v_nondep_3350_);
v___x_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3415_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3409_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3403_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3397_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = l_Lean_Json_mkObj(v___x_3424_);
lean_dec_ref_known(v___x_3424_, 2);
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3391_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v___x_3419_);
v___x_3428_ = l_Lean_Json_mkObj(v___x_3427_);
lean_dec_ref_known(v___x_3427_, 2);
v_fst_3048_ = v___x_3428_;
v_snd_3049_ = v_snd_3387_;
goto v___jp_3047_;
}
}
}
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
lean_del_object(v___x_3379_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3369_);
lean_dec(v_fst_3366_);
lean_del_object(v___x_3364_);
lean_del_object(v___x_3359_);
lean_dec(v_fst_3356_);
lean_del_object(v___x_3354_);
lean_dec_ref_known(v_e_2987_, 4);
return v___x_3381_;
}
}
}
}
else
{
lean_del_object(v___x_3369_);
lean_dec(v_fst_3366_);
lean_del_object(v___x_3364_);
lean_del_object(v___x_3359_);
lean_dec(v_fst_3356_);
lean_del_object(v___x_3354_);
lean_dec_ref_known(v_e_2987_, 4);
return v___x_3371_;
}
}
}
}
else
{
lean_del_object(v___x_3359_);
lean_dec(v_fst_3356_);
lean_del_object(v___x_3354_);
lean_dec_ref_known(v_e_2987_, 4);
return v___x_3361_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2987_, 4);
return v___x_3351_;
}
}
case 9:
{
lean_object* v_a_3445_; 
v_a_3445_ = lean_ctor_get(v_e_2987_, 0);
lean_inc_ref(v_a_3445_);
if (lean_obj_tag(v_a_3445_) == 0)
{
lean_object* v_val_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3477_; 
v_val_3446_ = lean_ctor_get(v_a_3445_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_a_3445_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3448_ = v_a_3445_;
v_isShared_3449_ = v_isSharedCheck_3477_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_val_3446_);
lean_dec(v_a_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3477_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; 
v___x_3450_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v_snd_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3467_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v_snd_3452_ = lean_ctor_get(v_a_3451_, 1);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_a_3451_);
if (v_isSharedCheck_3467_ == 0)
{
lean_object* v_unused_3468_; 
v_unused_3468_ = lean_ctor_get(v_a_3451_, 0);
lean_dec(v_unused_3468_);
v___x_3454_ = v_a_3451_;
v_isShared_3455_ = v_isSharedCheck_3467_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_snd_3452_);
lean_dec(v_a_3451_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3467_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3456_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__15));
v___x_3457_ = l_Nat_reprFast(v_val_3446_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set_tag(v___x_3448_, 3);
lean_ctor_set(v___x_3448_, 0, v___x_3457_);
v___x_3459_ = v___x_3448_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 1, v___x_3459_);
lean_ctor_set(v___x_3454_, 0, v___x_3456_);
v___x_3461_ = v___x_3454_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3462_ = lean_box(0);
v___x_3463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3461_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = l_Lean_Json_mkObj(v___x_3463_);
lean_dec_ref_known(v___x_3463_, 2);
v_fst_3048_ = v___x_3464_;
v_snd_3049_ = v_snd_3452_;
goto v___jp_3047_;
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_del_object(v___x_3448_);
lean_dec(v_val_3446_);
lean_dec_ref_known(v_e_2987_, 1);
v_a_3469_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3450_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3450_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
}
else
{
lean_object* v_val_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3508_; 
v_val_3478_ = lean_ctor_get(v_a_3445_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_a_3445_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3480_ = v_a_3445_;
v_isShared_3481_ = v_isSharedCheck_3508_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_val_3478_);
lean_dec(v_a_3445_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3508_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; 
v___x_3482_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v_snd_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3498_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref_known(v___x_3482_, 1);
v_snd_3484_ = lean_ctor_get(v_a_3483_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_a_3483_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; 
v_unused_3499_ = lean_ctor_get(v_a_3483_, 0);
lean_dec(v_unused_3499_);
v___x_3486_ = v_a_3483_;
v_isShared_3487_ = v_isSharedCheck_3498_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_snd_3484_);
lean_dec(v_a_3483_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3498_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3490_; 
v___x_3488_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__16));
if (v_isShared_3481_ == 0)
{
lean_ctor_set_tag(v___x_3480_, 3);
v___x_3490_ = v___x_3480_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_val_3478_);
v___x_3490_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3492_; 
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 1, v___x_3490_);
lean_ctor_set(v___x_3486_, 0, v___x_3488_);
v___x_3492_ = v___x_3486_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3493_ = lean_box(0);
v___x_3494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3492_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = l_Lean_Json_mkObj(v___x_3494_);
lean_dec_ref_known(v___x_3494_, 2);
v_fst_3048_ = v___x_3495_;
v_snd_3049_ = v_snd_3484_;
goto v___jp_3047_;
}
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_del_object(v___x_3480_);
lean_dec_ref(v_val_3478_);
lean_dec_ref_known(v_e_2987_, 1);
v_a_3500_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3482_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3482_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_3509_; lean_object* v_expr_3510_; lean_object* v___x_3511_; 
v_data_3509_ = lean_ctor_get(v_e_2987_, 0);
v_expr_3510_ = lean_ctor_get(v_e_2987_, 1);
lean_inc_ref(v_expr_3510_);
v___x_3511_ = l_LeanExport_dumpExprAux(v_expr_3510_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3541_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3541_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3541_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_fst_3516_; lean_object* v_snd_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3540_; 
v_fst_3516_ = lean_ctor_get(v_a_3512_, 0);
v_snd_3517_ = lean_ctor_get(v_a_3512_, 1);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_a_3512_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3519_ = v_a_3512_;
v_isShared_3520_ = v_isSharedCheck_3540_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_snd_3517_);
lean_inc(v_fst_3516_);
lean_dec(v_a_3512_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3540_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3521_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__17));
v___x_3522_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__18));
lean_inc(v_data_3509_);
v___x_3523_ = l___private_LeanExport_Basic_0__Lean_KVMap_toJson(v_data_3509_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v___x_3523_);
lean_ctor_set(v___x_3519_, 0, v___x_3522_);
v___x_3525_ = v___x_3519_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3526_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__19));
v___x_3527_ = l_Lean_JsonNumber_fromNat(v_fst_3516_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set_tag(v___x_3514_, 2);
lean_ctor_set(v___x_3514_, 0, v___x_3527_);
v___x_3529_ = v___x_3514_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3526_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = lean_box(0);
v___x_3532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3530_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3525_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = l_Lean_Json_mkObj(v___x_3533_);
lean_dec_ref_known(v___x_3533_, 2);
v___x_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3521_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
lean_ctor_set(v___x_3536_, 1, v___x_3531_);
v___x_3537_ = l_Lean_Json_mkObj(v___x_3536_);
lean_dec_ref_known(v___x_3536_, 2);
v_fst_3048_ = v___x_3537_;
v_snd_3049_ = v_snd_3517_;
goto v___jp_3047_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2987_, 2);
return v___x_3511_;
}
}
case 11:
{
lean_object* v_typeName_3542_; lean_object* v_idx_3543_; lean_object* v_struct_3544_; lean_object* v___x_3545_; 
v_typeName_3542_ = lean_ctor_get(v_e_2987_, 0);
v_idx_3543_ = lean_ctor_get(v_e_2987_, 1);
v_struct_3544_ = lean_ctor_get(v_e_2987_, 2);
lean_inc(v_typeName_3542_);
v___x_3545_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_typeName_3542_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3597_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3548_ = v___x_3545_;
v_isShared_3549_ = v_isSharedCheck_3597_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3545_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3597_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v_fst_3550_; lean_object* v_snd_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3596_; 
v_fst_3550_ = lean_ctor_get(v_a_3546_, 0);
v_snd_3551_ = lean_ctor_get(v_a_3546_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_a_3546_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3553_ = v_a_3546_;
v_isShared_3554_ = v_isSharedCheck_3596_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_snd_3551_);
lean_inc(v_fst_3550_);
lean_dec(v_a_3546_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3596_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; 
lean_inc_ref(v_struct_3544_);
v___x_3555_ = l_LeanExport_dumpExprAux(v_struct_3544_, v_a_2988_, v_snd_3551_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3595_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3595_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3595_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v_fst_3560_; lean_object* v_snd_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3594_; 
v_fst_3560_ = lean_ctor_get(v_a_3556_, 0);
v_snd_3561_ = lean_ctor_get(v_a_3556_, 1);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_a_3556_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3563_ = v_a_3556_;
v_isShared_3564_ = v_isSharedCheck_3594_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_snd_3561_);
lean_inc(v_fst_3560_);
lean_dec(v_a_3556_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3594_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
v___x_3565_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__20));
v___x_3566_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__21));
v___x_3567_ = l_Lean_JsonNumber_fromNat(v_fst_3550_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set_tag(v___x_3558_, 2);
lean_ctor_set(v___x_3558_, 0, v___x_3567_);
v___x_3569_ = v___x_3558_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3567_);
v___x_3569_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3571_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 1, v___x_3569_);
lean_ctor_set(v___x_3563_, 0, v___x_3566_);
v___x_3571_ = v___x_3563_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3572_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__22));
lean_inc(v_idx_3543_);
v___x_3573_ = l_Lean_JsonNumber_fromNat(v_idx_3543_);
if (v_isShared_3549_ == 0)
{
lean_ctor_set_tag(v___x_3548_, 2);
lean_ctor_set(v___x_3548_, 0, v___x_3573_);
v___x_3575_ = v___x_3548_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3577_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 1, v___x_3575_);
lean_ctor_set(v___x_3553_, 0, v___x_3572_);
v___x_3577_ = v___x_3553_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3578_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__23));
v___x_3579_ = l_Lean_JsonNumber_fromNat(v_fst_3560_);
v___x_3580_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
v___x_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3578_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = lean_box(0);
v___x_3583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3581_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3577_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3571_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = l_Lean_Json_mkObj(v___x_3585_);
lean_dec_ref_known(v___x_3585_, 2);
v___x_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3565_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
v___x_3588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
lean_ctor_set(v___x_3588_, 1, v___x_3582_);
v___x_3589_ = l_Lean_Json_mkObj(v___x_3588_);
lean_dec_ref_known(v___x_3588_, 2);
v_fst_3048_ = v___x_3589_;
v_snd_3049_ = v_snd_3561_;
goto v___jp_3047_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3553_);
lean_dec(v_fst_3550_);
lean_del_object(v___x_3548_);
lean_dec_ref_known(v_e_2987_, 3);
return v___x_3555_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2987_, 3);
return v___x_3545_;
}
}
default: 
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = lean_obj_once(&l_LeanExport_dumpExprAux___closed__26, &l_LeanExport_dumpExprAux___closed__26_once, _init_l_LeanExport_dumpExprAux___closed__26);
v___x_3599_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_3598_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v_fst_3601_; lean_object* v_snd_3602_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
v_fst_3601_ = lean_ctor_get(v_a_3600_, 0);
lean_inc(v_fst_3601_);
v_snd_3602_ = lean_ctor_get(v_a_3600_, 1);
lean_inc(v_snd_3602_);
lean_dec(v_a_3600_);
v_fst_3048_ = v_fst_3601_;
v_snd_3049_ = v_snd_3602_;
goto v___jp_3047_;
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec_ref(v_e_2987_);
v_a_3603_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3599_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3599_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
v___jp_3011_:
{
lean_object* v_size_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_size_3022_ = lean_ctor_get(v_visitedExprs_3015_, 0);
lean_inc_n(v_size_3022_, 2);
v___x_3023_ = l_Lean_JsonNumber_fromNat(v_size_3022_);
v___x_3024_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
v___x_3025_ = l_Lean_Json_setObjVal_x21(v_fst_3012_, v___x_3010_, v___x_3024_);
v___x_3026_ = l_Lean_Json_compress(v___x_3025_);
v___x_3027_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_3026_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3037_; 
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3037_ == 0)
{
lean_object* v_unused_3038_; 
v_unused_3038_ = lean_ctor_get(v___x_3027_, 0);
lean_dec(v_unused_3038_);
v___x_3029_ = v___x_3027_;
v_isShared_3030_ = v_isSharedCheck_3037_;
goto v_resetjp_3028_;
}
else
{
lean_dec(v___x_3027_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3037_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_inc(v_size_3022_);
v___x_3031_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_visitedExprs_3015_, v_e_2987_, v_size_3022_);
v___x_3032_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_3032_, 0, v_visitedNames_3013_);
lean_ctor_set(v___x_3032_, 1, v_visitedLevels_3014_);
lean_ctor_set(v___x_3032_, 2, v___x_3031_);
lean_ctor_set(v___x_3032_, 3, v_visitedConstants_3016_);
lean_ctor_set(v___x_3032_, 4, v_noMDataExprs_3017_);
lean_ctor_set(v___x_3032_, 5, v_recursorMap_3021_);
lean_ctor_set_uint8(v___x_3032_, sizeof(void*)*6, v_exportMData_3018_);
lean_ctor_set_uint8(v___x_3032_, sizeof(void*)*6 + 1, v_exportUnsafe_3019_);
lean_ctor_set_uint8(v___x_3032_, sizeof(void*)*6 + 2, v_ignoreMissing_3020_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v_size_3022_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3033_);
v___x_3035_ = v___x_3029_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec(v_size_3022_);
lean_dec(v_recursorMap_3021_);
lean_dec_ref(v_noMDataExprs_3017_);
lean_dec_ref(v_visitedConstants_3016_);
lean_dec_ref(v_visitedExprs_3015_);
lean_dec_ref(v_visitedLevels_3014_);
lean_dec_ref(v_visitedNames_3013_);
lean_dec_ref(v_e_2987_);
v_a_3039_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3027_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3027_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
v___jp_3047_:
{
lean_object* v_visitedNames_3050_; lean_object* v_visitedLevels_3051_; lean_object* v_visitedExprs_3052_; lean_object* v_visitedConstants_3053_; lean_object* v_noMDataExprs_3054_; uint8_t v_exportMData_3055_; uint8_t v_exportUnsafe_3056_; uint8_t v_ignoreMissing_3057_; lean_object* v_recursorMap_3058_; 
v_visitedNames_3050_ = lean_ctor_get(v_snd_3049_, 0);
lean_inc_ref(v_visitedNames_3050_);
v_visitedLevels_3051_ = lean_ctor_get(v_snd_3049_, 1);
lean_inc_ref(v_visitedLevels_3051_);
v_visitedExprs_3052_ = lean_ctor_get(v_snd_3049_, 2);
lean_inc_ref(v_visitedExprs_3052_);
v_visitedConstants_3053_ = lean_ctor_get(v_snd_3049_, 3);
lean_inc_ref(v_visitedConstants_3053_);
v_noMDataExprs_3054_ = lean_ctor_get(v_snd_3049_, 4);
lean_inc_ref(v_noMDataExprs_3054_);
v_exportMData_3055_ = lean_ctor_get_uint8(v_snd_3049_, sizeof(void*)*6);
v_exportUnsafe_3056_ = lean_ctor_get_uint8(v_snd_3049_, sizeof(void*)*6 + 1);
v_ignoreMissing_3057_ = lean_ctor_get_uint8(v_snd_3049_, sizeof(void*)*6 + 2);
v_recursorMap_3058_ = lean_ctor_get(v_snd_3049_, 5);
lean_inc(v_recursorMap_3058_);
lean_dec_ref(v_snd_3049_);
v_fst_3012_ = v_fst_3048_;
v_visitedNames_3013_ = v_visitedNames_3050_;
v_visitedLevels_3014_ = v_visitedLevels_3051_;
v_visitedExprs_3015_ = v_visitedExprs_3052_;
v_visitedConstants_3016_ = v_visitedConstants_3053_;
v_noMDataExprs_3017_ = v_noMDataExprs_3054_;
v_exportMData_3018_ = v_exportMData_3055_;
v_exportUnsafe_3019_ = v_exportUnsafe_3056_;
v_ignoreMissing_3020_ = v_ignoreMissing_3057_;
v_recursorMap_3021_ = v_recursorMap_3058_;
goto v___jp_3011_;
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr(lean_object* v_e_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_){
_start:
{
uint8_t v_exportMData_3615_; 
v_exportMData_3615_ = lean_ctor_get_uint8(v_a_3613_, sizeof(void*)*6);
if (v_exportMData_3615_ == 0)
{
lean_object* v_visitedNames_3616_; lean_object* v_visitedLevels_3617_; lean_object* v_visitedExprs_3618_; lean_object* v_visitedConstants_3619_; uint8_t v_exportUnsafe_3620_; uint8_t v_ignoreMissing_3621_; lean_object* v_recursorMap_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3643_; 
v_visitedNames_3616_ = lean_ctor_get(v_a_3613_, 0);
v_visitedLevels_3617_ = lean_ctor_get(v_a_3613_, 1);
v_visitedExprs_3618_ = lean_ctor_get(v_a_3613_, 2);
v_visitedConstants_3619_ = lean_ctor_get(v_a_3613_, 3);
v_exportUnsafe_3620_ = lean_ctor_get_uint8(v_a_3613_, sizeof(void*)*6 + 1);
v_ignoreMissing_3621_ = lean_ctor_get_uint8(v_a_3613_, sizeof(void*)*6 + 2);
v_recursorMap_3622_ = lean_ctor_get(v_a_3613_, 5);
v_isSharedCheck_3643_ = !lean_is_exclusive(v_a_3613_);
if (v_isSharedCheck_3643_ == 0)
{
lean_object* v_unused_3644_; 
v_unused_3644_ = lean_ctor_get(v_a_3613_, 4);
lean_dec(v_unused_3644_);
v___x_3624_ = v_a_3613_;
v_isShared_3625_ = v_isSharedCheck_3643_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_recursorMap_3622_);
lean_inc(v_visitedConstants_3619_);
lean_inc(v_visitedExprs_3618_);
lean_inc(v_visitedLevels_3617_);
lean_inc(v_visitedNames_3616_);
lean_dec(v_a_3613_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3643_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3626_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v___x_3626_);
v___x_3628_ = v___x_3624_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_visitedNames_3616_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_visitedLevels_3617_);
lean_ctor_set(v_reuseFailAlloc_3642_, 2, v_visitedExprs_3618_);
lean_ctor_set(v_reuseFailAlloc_3642_, 3, v_visitedConstants_3619_);
lean_ctor_set(v_reuseFailAlloc_3642_, 4, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3642_, 5, v_recursorMap_3622_);
lean_ctor_set_uint8(v_reuseFailAlloc_3642_, sizeof(void*)*6, v_exportMData_3615_);
lean_ctor_set_uint8(v_reuseFailAlloc_3642_, sizeof(void*)*6 + 1, v_exportUnsafe_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3642_, sizeof(void*)*6 + 2, v_ignoreMissing_3621_);
v___x_3628_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3629_; 
v___x_3629_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_3611_, v_a_3612_, v___x_3628_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v_fst_3631_; lean_object* v_snd_3632_; lean_object* v___x_3633_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3629_, 1);
v_fst_3631_ = lean_ctor_get(v_a_3630_, 0);
lean_inc(v_fst_3631_);
v_snd_3632_ = lean_ctor_get(v_a_3630_, 1);
lean_inc(v_snd_3632_);
lean_dec(v_a_3630_);
v___x_3633_ = l_LeanExport_dumpExprAux(v_fst_3631_, v_a_3612_, v_snd_3632_);
return v___x_3633_;
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
v_a_3634_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3629_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3629_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
}
}
else
{
lean_object* v___x_3645_; 
v___x_3645_ = l_LeanExport_dumpExprAux(v_e_3611_, v_a_3612_, v_a_3613_);
return v___x_3645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(size_t v_sz_3655_, size_t v_i_3656_, lean_object* v_bs_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
uint8_t v___x_3661_; 
v___x_3661_ = lean_usize_dec_lt(v_i_3656_, v_sz_3655_);
if (v___x_3661_ == 0)
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3662_, 0, v_bs_3657_);
lean_ctor_set(v___x_3662_, 1, v___y_3659_);
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
return v___x_3663_;
}
else
{
lean_object* v_v_3664_; lean_object* v_toConstantVal_3665_; lean_object* v_numParams_3666_; lean_object* v_numIndices_3667_; lean_object* v_all_3668_; lean_object* v_ctors_3669_; lean_object* v_numNested_3670_; uint8_t v_isRec_3671_; uint8_t v_isUnsafe_3672_; uint8_t v_isReflexive_3673_; lean_object* v_name_3674_; lean_object* v_levelParams_3675_; lean_object* v_type_3676_; lean_object* v___x_3677_; lean_object* v_bs_x27_3678_; lean_object* v___x_3679_; 
v_v_3664_ = lean_array_uget_borrowed(v_bs_3657_, v_i_3656_);
v_toConstantVal_3665_ = lean_ctor_get(v_v_3664_, 0);
v_numParams_3666_ = lean_ctor_get(v_v_3664_, 1);
lean_inc(v_numParams_3666_);
v_numIndices_3667_ = lean_ctor_get(v_v_3664_, 2);
lean_inc(v_numIndices_3667_);
v_all_3668_ = lean_ctor_get(v_v_3664_, 3);
lean_inc(v_all_3668_);
v_ctors_3669_ = lean_ctor_get(v_v_3664_, 4);
lean_inc(v_ctors_3669_);
v_numNested_3670_ = lean_ctor_get(v_v_3664_, 5);
lean_inc(v_numNested_3670_);
v_isRec_3671_ = lean_ctor_get_uint8(v_v_3664_, sizeof(void*)*6);
v_isUnsafe_3672_ = lean_ctor_get_uint8(v_v_3664_, sizeof(void*)*6 + 1);
v_isReflexive_3673_ = lean_ctor_get_uint8(v_v_3664_, sizeof(void*)*6 + 2);
v_name_3674_ = lean_ctor_get(v_toConstantVal_3665_, 0);
lean_inc(v_name_3674_);
v_levelParams_3675_ = lean_ctor_get(v_toConstantVal_3665_, 1);
lean_inc(v_levelParams_3675_);
v_type_3676_ = lean_ctor_get(v_toConstantVal_3665_, 2);
lean_inc_ref(v_type_3676_);
v___x_3677_ = lean_unsigned_to_nat(0u);
v_bs_x27_3678_ = lean_array_uset(v_bs_3657_, v_i_3656_, v___x_3677_);
v___x_3679_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3674_, v___y_3658_, v___y_3659_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v_fst_3681_; lean_object* v_snd_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3812_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v___x_3679_, 1);
v_fst_3681_ = lean_ctor_get(v_a_3680_, 0);
v_snd_3682_ = lean_ctor_get(v_a_3680_, 1);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_a_3680_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3684_ = v_a_3680_;
v_isShared_3685_ = v_isSharedCheck_3812_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_snd_3682_);
lean_inc(v_fst_3681_);
lean_dec(v_a_3680_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3812_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; 
v___x_3686_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3675_, v___y_3658_, v_snd_3682_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v_fst_3688_; lean_object* v_snd_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3803_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v_fst_3688_ = lean_ctor_get(v_a_3687_, 0);
v_snd_3689_ = lean_ctor_get(v_a_3687_, 1);
v_isSharedCheck_3803_ = !lean_is_exclusive(v_a_3687_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3691_ = v_a_3687_;
v_isShared_3692_ = v_isSharedCheck_3803_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_snd_3689_);
lean_inc(v_fst_3688_);
lean_dec(v_a_3687_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3803_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3693_; 
v___x_3693_ = l_LeanExport_dumpExpr(v_type_3676_, v___y_3658_, v_snd_3689_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v_fst_3695_; lean_object* v_snd_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3794_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v_fst_3695_ = lean_ctor_get(v_a_3694_, 0);
v_snd_3696_ = lean_ctor_get(v_a_3694_, 1);
v_isSharedCheck_3794_ = !lean_is_exclusive(v_a_3694_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3698_ = v_a_3694_;
v_isShared_3699_ = v_isSharedCheck_3794_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_snd_3696_);
lean_inc(v_fst_3695_);
lean_dec(v_a_3694_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3794_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; 
v___x_3700_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_3668_, v___y_3658_, v_snd_3696_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v_fst_3702_; lean_object* v_snd_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3785_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v_fst_3702_ = lean_ctor_get(v_a_3701_, 0);
v_snd_3703_ = lean_ctor_get(v_a_3701_, 1);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_a_3701_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3705_ = v_a_3701_;
v_isShared_3706_ = v_isSharedCheck_3785_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_snd_3703_);
lean_inc(v_fst_3702_);
lean_dec(v_a_3701_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3785_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; 
v___x_3707_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_ctors_3669_, v___y_3658_, v_snd_3703_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v_fst_3709_; lean_object* v_snd_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3776_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3707_, 1);
v_fst_3709_ = lean_ctor_get(v_a_3708_, 0);
v_snd_3710_ = lean_ctor_get(v_a_3708_, 1);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_a_3708_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3712_ = v_a_3708_;
v_isShared_3713_ = v_isSharedCheck_3776_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_snd_3710_);
lean_inc(v_fst_3709_);
lean_dec(v_a_3708_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3776_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3718_; 
v___x_3714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3715_ = l_Lean_JsonNumber_fromNat(v_fst_3681_);
v___x_3716_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 1, v___x_3716_);
lean_ctor_set(v___x_3712_, 0, v___x_3714_);
v___x_3718_ = v___x_3712_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
v___x_3719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 1, v_fst_3688_);
lean_ctor_set(v___x_3705_, 0, v___x_3719_);
v___x_3721_ = v___x_3705_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_fst_3688_);
v___x_3721_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
v___x_3722_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3723_ = l_Lean_JsonNumber_fromNat(v_fst_3695_);
v___x_3724_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 1, v___x_3724_);
lean_ctor_set(v___x_3698_, 0, v___x_3722_);
v___x_3726_ = v___x_3698_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_3728_ = l_Lean_JsonNumber_fromNat(v_numParams_3666_);
v___x_3729_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 1, v___x_3729_);
lean_ctor_set(v___x_3691_, 0, v___x_3727_);
v___x_3731_ = v___x_3691_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3736_; 
v___x_3732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0));
v___x_3733_ = l_Lean_JsonNumber_fromNat(v_numIndices_3667_);
v___x_3734_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 1, v___x_3734_);
lean_ctor_set(v___x_3684_, 0, v___x_3732_);
v___x_3736_ = v___x_3684_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; size_t v___x_3767_; size_t v___x_3768_; lean_object* v___x_3769_; 
v___x_3737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
v___x_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
lean_ctor_set(v___x_3738_, 1, v_fst_3702_);
v___x_3739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2));
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
lean_ctor_set(v___x_3740_, 1, v_fst_3709_);
v___x_3741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3));
v___x_3742_ = l_Lean_JsonNumber_fromNat(v_numNested_3670_);
v___x_3743_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3741_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4));
v___x_3746_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3746_, 0, v_isRec_3671_);
v___x_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5));
v___x_3749_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3749_, 0, v_isReflexive_3673_);
v___x_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_3752_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3752_, 0, v_isUnsafe_3672_);
v___x_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3751_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_box(0);
v___x_3755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3750_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3747_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3744_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3740_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3738_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3736_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3731_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3726_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3721_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3718_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_Json_mkObj(v___x_3765_);
lean_dec_ref_known(v___x_3765_, 2);
v___x_3767_ = ((size_t)1ULL);
v___x_3768_ = lean_usize_add(v_i_3656_, v___x_3767_);
v___x_3769_ = lean_array_uset(v_bs_x27_3678_, v_i_3656_, v___x_3766_);
v_i_3656_ = v___x_3768_;
v_bs_3657_ = v___x_3769_;
v___y_3659_ = v_snd_3710_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_del_object(v___x_3705_);
lean_dec(v_fst_3702_);
lean_del_object(v___x_3698_);
lean_dec(v_fst_3695_);
lean_del_object(v___x_3691_);
lean_dec(v_fst_3688_);
lean_del_object(v___x_3684_);
lean_dec(v_fst_3681_);
lean_dec_ref(v_bs_x27_3678_);
lean_dec(v_numNested_3670_);
lean_dec(v_numIndices_3667_);
lean_dec(v_numParams_3666_);
v_a_3777_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3707_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3707_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_del_object(v___x_3698_);
lean_dec(v_fst_3695_);
lean_del_object(v___x_3691_);
lean_dec(v_fst_3688_);
lean_del_object(v___x_3684_);
lean_dec(v_fst_3681_);
lean_dec_ref(v_bs_x27_3678_);
lean_dec(v_numNested_3670_);
lean_dec(v_ctors_3669_);
lean_dec(v_numIndices_3667_);
lean_dec(v_numParams_3666_);
v_a_3786_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3700_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3700_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_del_object(v___x_3691_);
lean_dec(v_fst_3688_);
lean_del_object(v___x_3684_);
lean_dec(v_fst_3681_);
lean_dec_ref(v_bs_x27_3678_);
lean_dec(v_numNested_3670_);
lean_dec(v_ctors_3669_);
lean_dec(v_all_3668_);
lean_dec(v_numIndices_3667_);
lean_dec(v_numParams_3666_);
v_a_3795_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3693_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3693_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_del_object(v___x_3684_);
lean_dec(v_fst_3681_);
lean_dec_ref(v_bs_x27_3678_);
lean_dec_ref(v_type_3676_);
lean_dec(v_numNested_3670_);
lean_dec(v_ctors_3669_);
lean_dec(v_all_3668_);
lean_dec(v_numIndices_3667_);
lean_dec(v_numParams_3666_);
v_a_3804_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3686_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3686_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec_ref(v_bs_x27_3678_);
lean_dec_ref(v_type_3676_);
lean_dec(v_levelParams_3675_);
lean_dec(v_numNested_3670_);
lean_dec(v_ctors_3669_);
lean_dec(v_all_3668_);
lean_dec(v_numIndices_3667_);
lean_dec(v_numParams_3666_);
v_a_3813_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3679_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3679_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(size_t v_sz_3824_, size_t v_i_3825_, lean_object* v_bs_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_usize_dec_lt(v_i_3825_, v_sz_3824_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3831_, 0, v_bs_3826_);
lean_ctor_set(v___x_3831_, 1, v___y_3828_);
v___x_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
return v___x_3832_;
}
else
{
lean_object* v_v_3833_; lean_object* v_toConstantVal_3834_; lean_object* v_induct_3835_; lean_object* v_cidx_3836_; lean_object* v_numParams_3837_; lean_object* v_numFields_3838_; uint8_t v_isUnsafe_3839_; lean_object* v_name_3840_; lean_object* v_levelParams_3841_; lean_object* v_type_3842_; lean_object* v___x_3843_; lean_object* v_bs_x27_3844_; lean_object* v___x_3845_; 
v_v_3833_ = lean_array_uget_borrowed(v_bs_3826_, v_i_3825_);
v_toConstantVal_3834_ = lean_ctor_get(v_v_3833_, 0);
v_induct_3835_ = lean_ctor_get(v_v_3833_, 1);
lean_inc(v_induct_3835_);
v_cidx_3836_ = lean_ctor_get(v_v_3833_, 2);
lean_inc(v_cidx_3836_);
v_numParams_3837_ = lean_ctor_get(v_v_3833_, 3);
lean_inc(v_numParams_3837_);
v_numFields_3838_ = lean_ctor_get(v_v_3833_, 4);
lean_inc(v_numFields_3838_);
v_isUnsafe_3839_ = lean_ctor_get_uint8(v_v_3833_, sizeof(void*)*5);
v_name_3840_ = lean_ctor_get(v_toConstantVal_3834_, 0);
lean_inc(v_name_3840_);
v_levelParams_3841_ = lean_ctor_get(v_toConstantVal_3834_, 1);
lean_inc(v_levelParams_3841_);
v_type_3842_ = lean_ctor_get(v_toConstantVal_3834_, 2);
lean_inc_ref(v_type_3842_);
v___x_3843_ = lean_unsigned_to_nat(0u);
v_bs_x27_3844_ = lean_array_uset(v_bs_3826_, v_i_3825_, v___x_3843_);
v___x_3845_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3840_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v_fst_3847_; lean_object* v_snd_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3951_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v_fst_3847_ = lean_ctor_get(v_a_3846_, 0);
v_snd_3848_ = lean_ctor_get(v_a_3846_, 1);
v_isSharedCheck_3951_ = !lean_is_exclusive(v_a_3846_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3850_ = v_a_3846_;
v_isShared_3851_ = v_isSharedCheck_3951_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_snd_3848_);
lean_inc(v_fst_3847_);
lean_dec(v_a_3846_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3951_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3852_; 
v___x_3852_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3841_, v___y_3827_, v_snd_3848_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v_fst_3854_; lean_object* v_snd_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3942_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v_fst_3854_ = lean_ctor_get(v_a_3853_, 0);
v_snd_3855_ = lean_ctor_get(v_a_3853_, 1);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_a_3853_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3857_ = v_a_3853_;
v_isShared_3858_ = v_isSharedCheck_3942_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_snd_3855_);
lean_inc(v_fst_3854_);
lean_dec(v_a_3853_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3942_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_LeanExport_dumpExpr(v_type_3842_, v___y_3827_, v_snd_3855_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v_fst_3861_; lean_object* v_snd_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3933_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___x_3859_, 1);
v_fst_3861_ = lean_ctor_get(v_a_3860_, 0);
v_snd_3862_ = lean_ctor_get(v_a_3860_, 1);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_a_3860_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3864_ = v_a_3860_;
v_isShared_3865_ = v_isSharedCheck_3933_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_snd_3862_);
lean_inc(v_fst_3861_);
lean_dec(v_a_3860_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3933_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3866_; 
v___x_3866_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_induct_3835_, v___y_3827_, v_snd_3862_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v_fst_3868_; lean_object* v_snd_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3924_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3866_, 1);
v_fst_3868_ = lean_ctor_get(v_a_3867_, 0);
v_snd_3869_ = lean_ctor_get(v_a_3867_, 1);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_a_3867_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3871_ = v_a_3867_;
v_isShared_3872_ = v_isSharedCheck_3924_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_snd_3869_);
lean_inc(v_fst_3868_);
lean_dec(v_a_3867_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3924_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
v___x_3873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3874_ = l_Lean_JsonNumber_fromNat(v_fst_3847_);
v___x_3875_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 1, v___x_3875_);
lean_ctor_set(v___x_3871_, 0, v___x_3873_);
v___x_3877_ = v___x_3871_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3873_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
lean_object* v___x_3878_; lean_object* v___x_3880_; 
v___x_3878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 1, v_fst_3854_);
lean_ctor_set(v___x_3864_, 0, v___x_3878_);
v___x_3880_ = v___x_3864_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_fst_3854_);
v___x_3880_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3885_; 
v___x_3881_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3882_ = l_Lean_JsonNumber_fromNat(v_fst_3861_);
v___x_3883_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 1, v___x_3883_);
lean_ctor_set(v___x_3857_, 0, v___x_3881_);
v___x_3885_ = v___x_3857_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3881_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3890_; 
v___x_3886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2));
v___x_3887_ = l_Lean_JsonNumber_fromNat(v_fst_3868_);
v___x_3888_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v___x_3888_);
lean_ctor_set(v___x_3850_, 0, v___x_3886_);
v___x_3890_ = v___x_3850_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3886_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; size_t v___x_3916_; size_t v___x_3917_; lean_object* v___x_3918_; 
v___x_3891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3));
v___x_3892_ = l_Lean_JsonNumber_fromNat(v_cidx_3836_);
v___x_3893_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
v___x_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3891_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_3896_ = l_Lean_JsonNumber_fromNat(v_numParams_3837_);
v___x_3897_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
v___x_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3895_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5));
v___x_3900_ = l_Lean_JsonNumber_fromNat(v_numFields_3838_);
v___x_3901_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
v___x_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3899_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_3904_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3904_, 0, v_isUnsafe_3839_);
v___x_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3903_);
lean_ctor_set(v___x_3905_, 1, v___x_3904_);
v___x_3906_ = lean_box(0);
v___x_3907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3905_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3902_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
v___x_3909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3898_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3894_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3890_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3885_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3880_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3877_);
lean_ctor_set(v___x_3914_, 1, v___x_3913_);
v___x_3915_ = l_Lean_Json_mkObj(v___x_3914_);
lean_dec_ref_known(v___x_3914_, 2);
v___x_3916_ = ((size_t)1ULL);
v___x_3917_ = lean_usize_add(v_i_3825_, v___x_3916_);
v___x_3918_ = lean_array_uset(v_bs_x27_3844_, v_i_3825_, v___x_3915_);
v_i_3825_ = v___x_3917_;
v_bs_3826_ = v___x_3918_;
v___y_3828_ = v_snd_3869_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_del_object(v___x_3864_);
lean_dec(v_fst_3861_);
lean_del_object(v___x_3857_);
lean_dec(v_fst_3854_);
lean_del_object(v___x_3850_);
lean_dec(v_fst_3847_);
lean_dec_ref(v_bs_x27_3844_);
lean_dec(v_numFields_3838_);
lean_dec(v_numParams_3837_);
lean_dec(v_cidx_3836_);
v_a_3925_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3866_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3866_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_del_object(v___x_3857_);
lean_dec(v_fst_3854_);
lean_del_object(v___x_3850_);
lean_dec(v_fst_3847_);
lean_dec_ref(v_bs_x27_3844_);
lean_dec(v_numFields_3838_);
lean_dec(v_numParams_3837_);
lean_dec(v_cidx_3836_);
lean_dec(v_induct_3835_);
v_a_3934_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3859_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3859_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_del_object(v___x_3850_);
lean_dec(v_fst_3847_);
lean_dec_ref(v_bs_x27_3844_);
lean_dec_ref(v_type_3842_);
lean_dec(v_numFields_3838_);
lean_dec(v_numParams_3837_);
lean_dec(v_cidx_3836_);
lean_dec(v_induct_3835_);
v_a_3943_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3852_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3852_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
else
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3959_; 
lean_dec_ref(v_bs_x27_3844_);
lean_dec_ref(v_type_3842_);
lean_dec(v_levelParams_3841_);
lean_dec(v_numFields_3838_);
lean_dec(v_numParams_3837_);
lean_dec(v_cidx_3836_);
lean_dec(v_induct_3835_);
v_a_3952_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3954_ = v___x_3845_;
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3845_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object* v_rule_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_ctor_3966_; lean_object* v_nfields_3967_; lean_object* v_rhs_3968_; lean_object* v___x_3969_; 
v_ctor_3966_ = lean_ctor_get(v_rule_3962_, 0);
lean_inc(v_ctor_3966_);
v_nfields_3967_ = lean_ctor_get(v_rule_3962_, 1);
lean_inc(v_nfields_3967_);
v_rhs_3968_ = lean_ctor_get(v_rule_3962_, 2);
lean_inc_ref(v_rhs_3968_);
lean_dec_ref(v_rule_3962_);
v___x_3969_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_ctor_3966_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v_fst_3971_; lean_object* v_snd_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_4021_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref_known(v___x_3969_, 1);
v_fst_3971_ = lean_ctor_get(v_a_3970_, 0);
v_snd_3972_ = lean_ctor_get(v_a_3970_, 1);
v_isSharedCheck_4021_ = !lean_is_exclusive(v_a_3970_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_3974_ = v_a_3970_;
v_isShared_3975_ = v_isSharedCheck_4021_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_snd_3972_);
lean_inc(v_fst_3971_);
lean_dec(v_a_3970_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_4021_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_LeanExport_dumpExpr(v_rhs_3968_, v_a_3963_, v_snd_3972_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_4012_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_4012_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3976_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_4012_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v_fst_3981_; lean_object* v_snd_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4011_; 
v_fst_3981_ = lean_ctor_get(v_a_3977_, 0);
v_snd_3982_ = lean_ctor_get(v_a_3977_, 1);
v_isSharedCheck_4011_ = !lean_is_exclusive(v_a_3977_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_3984_ = v_a_3977_;
v_isShared_3985_ = v_isSharedCheck_4011_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_snd_3982_);
lean_inc(v_fst_3981_);
lean_dec(v_a_3977_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4011_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
v___x_3986_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2));
v___x_3987_ = l_Lean_JsonNumber_fromNat(v_fst_3971_);
v___x_3988_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 1, v___x_3988_);
lean_ctor_set(v___x_3984_, 0, v___x_3986_);
v___x_3990_ = v___x_3984_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_3986_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_4010_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3995_; 
v___x_3991_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0));
v___x_3992_ = l_Lean_JsonNumber_fromNat(v_nfields_3967_);
v___x_3993_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_3993_);
lean_ctor_set(v___x_3974_, 0, v___x_3991_);
v___x_3995_ = v___x_3974_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_4009_, 1, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_4009_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4007_; 
v___x_3996_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1));
v___x_3997_ = l_Lean_JsonNumber_fromNat(v_fst_3981_);
v___x_3998_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
v___x_3999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3996_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = lean_box(0);
v___x_4001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3999_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_3995_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_3990_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = l_Lean_Json_mkObj(v___x_4003_);
lean_dec_ref_known(v___x_4003_, 2);
v___x_4005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
lean_ctor_set(v___x_4005_, 1, v_snd_3982_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 0, v___x_4005_);
v___x_4007_ = v___x_3979_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_del_object(v___x_3974_);
lean_dec(v_fst_3971_);
lean_dec(v_nfields_3967_);
v_a_4013_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_3976_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_3976_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec_ref(v_rhs_3968_);
lean_dec(v_nfields_3967_);
v_a_4022_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_3969_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_3969_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object* v_x_4030_, lean_object* v_x_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
if (lean_obj_tag(v_x_4030_) == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = l_List_reverse___redArg(v_x_4031_);
v___x_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
lean_ctor_set(v___x_4036_, 1, v___y_4033_);
v___x_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4036_);
return v___x_4037_;
}
else
{
lean_object* v_head_4038_; lean_object* v_tail_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4059_; 
v_head_4038_ = lean_ctor_get(v_x_4030_, 0);
v_tail_4039_ = lean_ctor_get(v_x_4030_, 1);
v_isSharedCheck_4059_ = !lean_is_exclusive(v_x_4030_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4041_ = v_x_4030_;
v_isShared_4042_ = v_isSharedCheck_4059_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_tail_4039_);
lean_inc(v_head_4038_);
lean_dec(v_x_4030_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4059_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4043_; 
v___x_4043_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_head_4038_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v_fst_4045_; lean_object* v_snd_4046_; lean_object* v___x_4048_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
v_fst_4045_ = lean_ctor_get(v_a_4044_, 0);
lean_inc(v_fst_4045_);
v_snd_4046_ = lean_ctor_get(v_a_4044_, 1);
lean_inc(v_snd_4046_);
lean_dec(v_a_4044_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 1, v_x_4031_);
lean_ctor_set(v___x_4041_, 0, v_fst_4045_);
v___x_4048_ = v___x_4041_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_fst_4045_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v_x_4031_);
v___x_4048_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
v_x_4030_ = v_tail_4039_;
v_x_4031_ = v___x_4048_;
v___y_4033_ = v_snd_4046_;
goto _start;
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_del_object(v___x_4041_);
lean_dec(v_tail_4039_);
lean_dec(v_x_4031_);
v_a_4051_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4043_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4043_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t v_sz_4064_, size_t v_i_4065_, lean_object* v_bs_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
uint8_t v___x_4070_; 
v___x_4070_ = lean_usize_dec_lt(v_i_4065_, v_sz_4064_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4071_, 0, v_bs_4066_);
lean_ctor_set(v___x_4071_, 1, v___y_4068_);
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
return v___x_4072_;
}
else
{
lean_object* v_v_4073_; lean_object* v_toConstantVal_4074_; lean_object* v_all_4075_; lean_object* v_numParams_4076_; lean_object* v_numIndices_4077_; lean_object* v_numMotives_4078_; lean_object* v_numMinors_4079_; lean_object* v_rules_4080_; uint8_t v_k_4081_; uint8_t v_isUnsafe_4082_; lean_object* v_name_4083_; lean_object* v_levelParams_4084_; lean_object* v_type_4085_; lean_object* v___x_4086_; lean_object* v_bs_x27_4087_; lean_object* v___x_4088_; 
v_v_4073_ = lean_array_uget_borrowed(v_bs_4066_, v_i_4065_);
v_toConstantVal_4074_ = lean_ctor_get(v_v_4073_, 0);
v_all_4075_ = lean_ctor_get(v_v_4073_, 1);
lean_inc(v_all_4075_);
v_numParams_4076_ = lean_ctor_get(v_v_4073_, 2);
lean_inc(v_numParams_4076_);
v_numIndices_4077_ = lean_ctor_get(v_v_4073_, 3);
lean_inc(v_numIndices_4077_);
v_numMotives_4078_ = lean_ctor_get(v_v_4073_, 4);
lean_inc(v_numMotives_4078_);
v_numMinors_4079_ = lean_ctor_get(v_v_4073_, 5);
lean_inc(v_numMinors_4079_);
v_rules_4080_ = lean_ctor_get(v_v_4073_, 6);
lean_inc(v_rules_4080_);
v_k_4081_ = lean_ctor_get_uint8(v_v_4073_, sizeof(void*)*7);
v_isUnsafe_4082_ = lean_ctor_get_uint8(v_v_4073_, sizeof(void*)*7 + 1);
v_name_4083_ = lean_ctor_get(v_toConstantVal_4074_, 0);
lean_inc(v_name_4083_);
v_levelParams_4084_ = lean_ctor_get(v_toConstantVal_4074_, 1);
lean_inc(v_levelParams_4084_);
v_type_4085_ = lean_ctor_get(v_toConstantVal_4074_, 2);
lean_inc_ref(v_type_4085_);
v___x_4086_ = lean_unsigned_to_nat(0u);
v_bs_x27_4087_ = lean_array_uset(v_bs_4066_, v_i_4065_, v___x_4086_);
v___x_4088_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4083_, v___y_4067_, v___y_4068_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v_fst_4090_; lean_object* v_snd_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4223_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___x_4088_, 1);
v_fst_4090_ = lean_ctor_get(v_a_4089_, 0);
v_snd_4091_ = lean_ctor_get(v_a_4089_, 1);
v_isSharedCheck_4223_ = !lean_is_exclusive(v_a_4089_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4093_ = v_a_4089_;
v_isShared_4094_ = v_isSharedCheck_4223_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_snd_4091_);
lean_inc(v_fst_4090_);
lean_dec(v_a_4089_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4223_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4095_; 
v___x_4095_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4084_, v___y_4067_, v_snd_4091_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v_fst_4097_; lean_object* v_snd_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4214_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v___x_4095_, 1);
v_fst_4097_ = lean_ctor_get(v_a_4096_, 0);
v_snd_4098_ = lean_ctor_get(v_a_4096_, 1);
v_isSharedCheck_4214_ = !lean_is_exclusive(v_a_4096_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4100_ = v_a_4096_;
v_isShared_4101_ = v_isSharedCheck_4214_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_snd_4098_);
lean_inc(v_fst_4097_);
lean_dec(v_a_4096_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4214_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_LeanExport_dumpExpr(v_type_4085_, v___y_4067_, v_snd_4098_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v_fst_4104_; lean_object* v_snd_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4205_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v___x_4102_, 1);
v_fst_4104_ = lean_ctor_get(v_a_4103_, 0);
v_snd_4105_ = lean_ctor_get(v_a_4103_, 1);
v_isSharedCheck_4205_ = !lean_is_exclusive(v_a_4103_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4107_ = v_a_4103_;
v_isShared_4108_ = v_isSharedCheck_4205_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_snd_4105_);
lean_inc(v_fst_4104_);
lean_dec(v_a_4103_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4205_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4109_; 
v___x_4109_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_4075_, v___y_4067_, v_snd_4105_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v_fst_4111_; lean_object* v_snd_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4196_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4109_, 1);
v_fst_4111_ = lean_ctor_get(v_a_4110_, 0);
v_snd_4112_ = lean_ctor_get(v_a_4110_, 1);
v_isSharedCheck_4196_ = !lean_is_exclusive(v_a_4110_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4114_ = v_a_4110_;
v_isShared_4115_ = v_isSharedCheck_4196_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_snd_4112_);
lean_inc(v_fst_4111_);
lean_dec(v_a_4110_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4196_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4116_ = lean_box(0);
v___x_4117_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_rules_4080_, v___x_4116_, v___y_4067_, v_snd_4112_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v_fst_4119_; lean_object* v_snd_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4187_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref_known(v___x_4117_, 1);
v_fst_4119_ = lean_ctor_get(v_a_4118_, 0);
v_snd_4120_ = lean_ctor_get(v_a_4118_, 1);
v_isSharedCheck_4187_ = !lean_is_exclusive(v_a_4118_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4122_ = v_a_4118_;
v_isShared_4123_ = v_isSharedCheck_4187_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_snd_4120_);
lean_inc(v_fst_4119_);
lean_dec(v_a_4118_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4187_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4128_; 
v___x_4124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4125_ = l_Lean_JsonNumber_fromNat(v_fst_4090_);
v___x_4126_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 1, v___x_4126_);
lean_ctor_set(v___x_4122_, 0, v___x_4124_);
v___x_4128_ = v___x_4122_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v___x_4126_);
v___x_4128_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 1, v_fst_4097_);
lean_ctor_set(v___x_4114_, 0, v___x_4129_);
v___x_4131_ = v___x_4114_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4185_, 1, v_fst_4097_);
v___x_4131_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
v___x_4132_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4133_ = l_Lean_JsonNumber_fromNat(v_fst_4104_);
v___x_4134_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4133_);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 1, v___x_4134_);
lean_ctor_set(v___x_4107_, 0, v___x_4132_);
v___x_4136_ = v___x_4107_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4132_);
lean_ctor_set(v_reuseFailAlloc_4184_, 1, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4137_; lean_object* v___x_4139_; 
v___x_4137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 1, v_fst_4111_);
lean_ctor_set(v___x_4100_, 0, v___x_4137_);
v___x_4139_ = v___x_4100_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4137_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v_fst_4111_);
v___x_4139_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4144_; 
v___x_4140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_4141_ = l_Lean_JsonNumber_fromNat(v_numParams_4076_);
v___x_4142_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 1, v___x_4142_);
lean_ctor_set(v___x_4093_, 0, v___x_4140_);
v___x_4144_ = v___x_4093_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4140_);
lean_ctor_set(v_reuseFailAlloc_4182_, 1, v___x_4142_);
v___x_4144_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; size_t v___x_4178_; size_t v___x_4179_; lean_object* v___x_4180_; 
v___x_4145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0));
v___x_4146_ = l_Lean_JsonNumber_fromNat(v_numIndices_4077_);
v___x_4147_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
v___x_4148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4145_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0));
v___x_4150_ = l_Lean_JsonNumber_fromNat(v_numMotives_4078_);
v___x_4151_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
v___x_4152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4149_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
v___x_4153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
v___x_4154_ = l_Lean_JsonNumber_fromNat(v_numMinors_4079_);
v___x_4155_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
v___x_4156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4153_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2));
v___x_4158_ = l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(v_fst_4119_);
v___x_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3));
v___x_4161_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4161_, 0, v_k_4081_);
v___x_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4160_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
v___x_4163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_4164_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4164_, 0, v_isUnsafe_4082_);
v___x_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4163_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
lean_ctor_set(v___x_4166_, 1, v___x_4116_);
v___x_4167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4162_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4159_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v___x_4169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4156_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4152_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
v___x_4171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4148_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4144_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
v___x_4173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4139_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
v___x_4174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4136_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
v___x_4175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4131_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
v___x_4176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4128_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = l_Lean_Json_mkObj(v___x_4176_);
lean_dec_ref_known(v___x_4176_, 2);
v___x_4178_ = ((size_t)1ULL);
v___x_4179_ = lean_usize_add(v_i_4065_, v___x_4178_);
v___x_4180_ = lean_array_uset(v_bs_x27_4087_, v_i_4065_, v___x_4177_);
v_i_4065_ = v___x_4179_;
v_bs_4066_ = v___x_4180_;
v___y_4068_ = v_snd_4120_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
lean_del_object(v___x_4114_);
lean_dec(v_fst_4111_);
lean_del_object(v___x_4107_);
lean_dec(v_fst_4104_);
lean_del_object(v___x_4100_);
lean_dec(v_fst_4097_);
lean_del_object(v___x_4093_);
lean_dec(v_fst_4090_);
lean_dec_ref(v_bs_x27_4087_);
lean_dec(v_numMinors_4079_);
lean_dec(v_numMotives_4078_);
lean_dec(v_numIndices_4077_);
lean_dec(v_numParams_4076_);
v_a_4188_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4117_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4117_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
}
else
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
lean_del_object(v___x_4107_);
lean_dec(v_fst_4104_);
lean_del_object(v___x_4100_);
lean_dec(v_fst_4097_);
lean_del_object(v___x_4093_);
lean_dec(v_fst_4090_);
lean_dec_ref(v_bs_x27_4087_);
lean_dec(v_rules_4080_);
lean_dec(v_numMinors_4079_);
lean_dec(v_numMotives_4078_);
lean_dec(v_numIndices_4077_);
lean_dec(v_numParams_4076_);
v_a_4197_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4109_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4109_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_del_object(v___x_4100_);
lean_dec(v_fst_4097_);
lean_del_object(v___x_4093_);
lean_dec(v_fst_4090_);
lean_dec_ref(v_bs_x27_4087_);
lean_dec(v_rules_4080_);
lean_dec(v_numMinors_4079_);
lean_dec(v_numMotives_4078_);
lean_dec(v_numIndices_4077_);
lean_dec(v_numParams_4076_);
lean_dec(v_all_4075_);
v_a_4206_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4102_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4102_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_del_object(v___x_4093_);
lean_dec(v_fst_4090_);
lean_dec_ref(v_bs_x27_4087_);
lean_dec_ref(v_type_4085_);
lean_dec(v_rules_4080_);
lean_dec(v_numMinors_4079_);
lean_dec(v_numMotives_4078_);
lean_dec(v_numIndices_4077_);
lean_dec(v_numParams_4076_);
lean_dec(v_all_4075_);
v_a_4215_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4095_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4095_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec_ref(v_bs_x27_4087_);
lean_dec_ref(v_type_4085_);
lean_dec(v_levelParams_4084_);
lean_dec(v_rules_4080_);
lean_dec(v_numMinors_4079_);
lean_dec(v_numMotives_4078_);
lean_dec(v_numIndices_4077_);
lean_dec(v_numParams_4076_);
lean_dec(v_all_4075_);
v_a_4224_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4088_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4088_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(uint8_t v___x_4280_, lean_object* v_as_x27_4281_, lean_object* v_b_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
if (lean_obj_tag(v_as_x27_4281_) == 0)
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4286_, 0, v_b_4282_);
lean_ctor_set(v___x_4286_, 1, v___y_4284_);
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
return v___x_4287_;
}
else
{
lean_object* v_head_4288_; lean_object* v_tail_4289_; lean_object* v___x_4290_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___x_4321_; 
lean_dec_ref(v_b_4282_);
v_head_4288_ = lean_ctor_get(v_as_x27_4281_, 0);
v_tail_4289_ = lean_ctor_get(v_as_x27_4281_, 1);
v___x_4290_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
lean_inc(v_head_4288_);
lean_inc_ref(v___y_4283_);
v___x_4321_ = l_Lean_Environment_find_x3f(v___y_4283_, v_head_4288_, v___x_4280_);
if (lean_obj_tag(v___x_4321_) == 1)
{
lean_object* v_val_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4445_; 
v_val_4322_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4324_ = v___x_4321_;
v_isShared_4325_ = v_isSharedCheck_4445_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_val_4322_);
lean_dec(v___x_4321_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4445_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
if (lean_obj_tag(v_val_4322_) == 4)
{
lean_object* v_val_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4444_; 
v_val_4326_ = lean_ctor_get(v_val_4322_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v_val_4322_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4328_ = v_val_4322_;
v_isShared_4329_ = v_isSharedCheck_4444_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_val_4326_);
lean_dec(v_val_4322_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4444_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v_toConstantVal_4330_; lean_object* v_visitedNames_4331_; lean_object* v_visitedLevels_4332_; lean_object* v_visitedExprs_4333_; lean_object* v_visitedConstants_4334_; lean_object* v_noMDataExprs_4335_; uint8_t v_exportMData_4336_; uint8_t v_exportUnsafe_4337_; uint8_t v_ignoreMissing_4338_; lean_object* v_recursorMap_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4443_; 
v_toConstantVal_4330_ = lean_ctor_get(v_val_4326_, 0);
lean_inc_ref(v_toConstantVal_4330_);
v_visitedNames_4331_ = lean_ctor_get(v___y_4284_, 0);
v_visitedLevels_4332_ = lean_ctor_get(v___y_4284_, 1);
v_visitedExprs_4333_ = lean_ctor_get(v___y_4284_, 2);
v_visitedConstants_4334_ = lean_ctor_get(v___y_4284_, 3);
v_noMDataExprs_4335_ = lean_ctor_get(v___y_4284_, 4);
v_exportMData_4336_ = lean_ctor_get_uint8(v___y_4284_, sizeof(void*)*6);
v_exportUnsafe_4337_ = lean_ctor_get_uint8(v___y_4284_, sizeof(void*)*6 + 1);
v_ignoreMissing_4338_ = lean_ctor_get_uint8(v___y_4284_, sizeof(void*)*6 + 2);
v_recursorMap_4339_ = lean_ctor_get(v___y_4284_, 5);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___y_4284_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4341_ = v___y_4284_;
v_isShared_4342_ = v_isSharedCheck_4443_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_recursorMap_4339_);
lean_inc(v_noMDataExprs_4335_);
lean_inc(v_visitedConstants_4334_);
lean_inc(v_visitedExprs_4333_);
lean_inc(v_visitedLevels_4332_);
lean_inc(v_visitedNames_4331_);
lean_dec(v___y_4284_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4443_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
uint8_t v_kind_4343_; lean_object* v_name_4344_; lean_object* v_levelParams_4345_; lean_object* v_type_4346_; lean_object* v___x_4347_; lean_object* v___x_4349_; 
v_kind_4343_ = lean_ctor_get_uint8(v_val_4326_, sizeof(void*)*1);
lean_dec_ref(v_val_4326_);
v_name_4344_ = lean_ctor_get(v_toConstantVal_4330_, 0);
lean_inc(v_name_4344_);
v_levelParams_4345_ = lean_ctor_get(v_toConstantVal_4330_, 1);
lean_inc(v_levelParams_4345_);
v_type_4346_ = lean_ctor_get(v_toConstantVal_4330_, 2);
lean_inc_ref(v_type_4346_);
lean_dec_ref(v_toConstantVal_4330_);
lean_inc(v_head_4288_);
v___x_4347_ = l_Lean_NameHashSet_insert(v_visitedConstants_4334_, v_head_4288_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 3, v___x_4347_);
v___x_4349_ = v___x_4341_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_visitedNames_4331_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_visitedLevels_4332_);
lean_ctor_set(v_reuseFailAlloc_4442_, 2, v_visitedExprs_4333_);
lean_ctor_set(v_reuseFailAlloc_4442_, 3, v___x_4347_);
lean_ctor_set(v_reuseFailAlloc_4442_, 4, v_noMDataExprs_4335_);
lean_ctor_set(v_reuseFailAlloc_4442_, 5, v_recursorMap_4339_);
lean_ctor_set_uint8(v_reuseFailAlloc_4442_, sizeof(void*)*6, v_exportMData_4336_);
lean_ctor_set_uint8(v_reuseFailAlloc_4442_, sizeof(void*)*6 + 1, v_exportUnsafe_4337_);
lean_ctor_set_uint8(v_reuseFailAlloc_4442_, sizeof(void*)*6 + 2, v_ignoreMissing_4338_);
v___x_4349_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
lean_object* v___x_4350_; 
v___x_4350_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4344_, v___y_4283_, v___x_4349_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v_fst_4352_; lean_object* v_snd_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4433_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v_fst_4352_ = lean_ctor_get(v_a_4351_, 0);
v_snd_4353_ = lean_ctor_get(v_a_4351_, 1);
v_isSharedCheck_4433_ = !lean_is_exclusive(v_a_4351_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4355_ = v_a_4351_;
v_isShared_4356_ = v_isSharedCheck_4433_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_snd_4353_);
lean_inc(v_fst_4352_);
lean_dec(v_a_4351_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4433_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4357_; 
v___x_4357_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4345_, v___y_4283_, v_snd_4353_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v_fst_4359_; lean_object* v_snd_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4424_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v_fst_4359_ = lean_ctor_get(v_a_4358_, 0);
v_snd_4360_ = lean_ctor_get(v_a_4358_, 1);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_a_4358_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4362_ = v_a_4358_;
v_isShared_4363_ = v_isSharedCheck_4424_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_snd_4360_);
lean_inc(v_fst_4359_);
lean_dec(v_a_4358_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4424_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4364_; 
v___x_4364_ = l_LeanExport_dumpExpr(v_type_4346_, v___y_4283_, v_snd_4360_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v_fst_4366_; lean_object* v_snd_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4415_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___x_4364_, 1);
v_fst_4366_ = lean_ctor_get(v_a_4365_, 0);
v_snd_4367_ = lean_ctor_get(v_a_4365_, 1);
v_isSharedCheck_4415_ = !lean_is_exclusive(v_a_4365_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4369_ = v_a_4365_;
v_isShared_4370_ = v_isSharedCheck_4415_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_snd_4367_);
lean_inc(v_fst_4366_);
lean_dec(v_a_4365_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4415_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4375_; 
v___x_4371_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5));
v___x_4372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4373_ = l_Lean_JsonNumber_fromNat(v_fst_4352_);
if (v_isShared_4329_ == 0)
{
lean_ctor_set_tag(v___x_4328_, 2);
lean_ctor_set(v___x_4328_, 0, v___x_4373_);
v___x_4375_ = v___x_4328_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4373_);
v___x_4375_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
lean_object* v___x_4377_; 
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 1, v___x_4375_);
lean_ctor_set(v___x_4369_, 0, v___x_4372_);
v___x_4377_ = v___x_4369_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v___x_4375_);
v___x_4377_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
lean_object* v___x_4378_; lean_object* v___x_4380_; 
v___x_4378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 1, v_fst_4359_);
lean_ctor_set(v___x_4362_, 0, v___x_4378_);
v___x_4380_ = v___x_4362_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4378_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_fst_4359_);
v___x_4380_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4384_; 
v___x_4381_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4382_ = l_Lean_JsonNumber_fromNat(v_fst_4366_);
if (v_isShared_4325_ == 0)
{
lean_ctor_set_tag(v___x_4324_, 2);
lean_ctor_set(v___x_4324_, 0, v___x_4382_);
v___x_4384_ = v___x_4324_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4382_);
v___x_4384_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
lean_object* v___x_4386_; 
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 1, v___x_4384_);
lean_ctor_set(v___x_4355_, 0, v___x_4381_);
v___x_4386_ = v___x_4355_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4381_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v___x_4384_);
v___x_4386_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4387_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6));
v___x_4388_ = l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(v_kind_4343_);
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = lean_box(0);
v___x_4391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4386_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4380_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4377_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
v___x_4395_ = l_Lean_Json_mkObj(v___x_4394_);
lean_dec_ref_known(v___x_4394_, 2);
v___x_4396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4371_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
lean_ctor_set(v___x_4397_, 1, v___x_4390_);
v___x_4398_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4397_, v_snd_4367_);
lean_dec_ref_known(v___x_4397_, 2);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v_snd_4400_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v_snd_4400_ = lean_ctor_get(v_a_4399_, 1);
lean_inc(v_snd_4400_);
lean_dec(v_a_4399_);
v_as_x27_4281_ = v_tail_4289_;
v_b_4282_ = v___x_4290_;
v___y_4284_ = v_snd_4400_;
goto _start;
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
v_a_4402_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4398_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4398_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
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
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_del_object(v___x_4362_);
lean_dec(v_fst_4359_);
lean_del_object(v___x_4355_);
lean_dec(v_fst_4352_);
lean_del_object(v___x_4328_);
lean_del_object(v___x_4324_);
v_a_4416_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4364_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4364_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_del_object(v___x_4355_);
lean_dec(v_fst_4352_);
lean_dec_ref(v_type_4346_);
lean_del_object(v___x_4328_);
lean_del_object(v___x_4324_);
v_a_4425_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4357_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4357_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec_ref(v_type_4346_);
lean_dec(v_levelParams_4345_);
lean_del_object(v___x_4328_);
lean_del_object(v___x_4324_);
v_a_4434_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4350_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4350_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_4324_);
lean_dec(v_val_4322_);
v___y_4292_ = v___y_4283_;
v___y_4293_ = v___y_4284_;
goto v___jp_4291_;
}
}
}
else
{
lean_dec(v___x_4321_);
v___y_4292_ = v___y_4283_;
v___y_4293_ = v___y_4284_;
goto v___jp_4291_;
}
v___jp_4291_:
{
uint8_t v_ignoreMissing_4294_; 
v_ignoreMissing_4294_ = lean_ctor_get_uint8(v___y_4293_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_4294_ == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4295_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4296_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4297_ = lean_unsigned_to_nat(313u);
v___x_4298_ = lean_unsigned_to_nat(52u);
v___x_4299_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_4300_ = 1;
lean_inc(v_head_4288_);
v___x_4301_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_4288_, v___x_4300_);
v___x_4302_ = lean_string_append(v___x_4299_, v___x_4301_);
lean_dec_ref(v___x_4301_);
v___x_4303_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_4304_ = lean_string_append(v___x_4302_, v___x_4303_);
v___x_4305_ = l_mkPanicMessageWithDecl(v___x_4295_, v___x_4296_, v___x_4297_, v___x_4298_, v___x_4304_);
lean_dec_ref(v___x_4304_);
v___x_4306_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_4305_, v___y_4292_, v___y_4293_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v_snd_4308_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v_snd_4308_ = lean_ctor_get(v_a_4307_, 1);
lean_inc(v_snd_4308_);
lean_dec(v_a_4307_);
v_as_x27_4281_ = v_tail_4289_;
v_b_4282_ = v___x_4290_;
v___y_4284_ = v_snd_4308_;
goto _start;
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
v_a_4310_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4306_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4306_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
else
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4318_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4));
v___x_4319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
lean_ctor_set(v___x_4319_, 1, v___y_4293_);
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
return v___x_4320_;
}
}
}
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__21(void){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4448_ = l_Lean_NameSet_empty;
v___x_4449_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4449_);
lean_ctor_set(v___x_4450_, 1, v___x_4448_);
return v___x_4450_;
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__22(void){
_start:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4451_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__21, &l_LeanExport_dumpConstant___closed__21_once, _init_l_LeanExport_dumpConstant___closed__21);
v___x_4452_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
lean_ctor_set(v___x_4453_, 1, v___x_4451_);
return v___x_4453_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4456_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1));
v___x_4457_ = lean_unsigned_to_nat(11u);
v___x_4458_ = lean_unsigned_to_nat(341u);
v___x_4459_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4460_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4461_ = l_mkPanicMessageWithDecl(v___x_4460_, v___x_4459_, v___x_4458_, v___x_4457_, v___x_4456_);
return v___x_4461_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4463_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3));
v___x_4464_ = lean_unsigned_to_nat(6u);
v___x_4465_ = lean_unsigned_to_nat(329u);
v___x_4466_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4467_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4468_ = l_mkPanicMessageWithDecl(v___x_4467_, v___x_4466_, v___x_4465_, v___x_4464_, v___x_4463_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(uint8_t v___x_4469_, lean_object* v_val_4470_, lean_object* v_as_x27_4471_, lean_object* v_b_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_){
_start:
{
if (lean_obj_tag(v_as_x27_4471_) == 0)
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4476_, 0, v_b_4472_);
lean_ctor_set(v___x_4476_, 1, v___y_4474_);
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
return v___x_4477_;
}
else
{
lean_object* v_head_4478_; lean_object* v_tail_4479_; lean_object* v___y_4481_; lean_object* v_snd_4512_; lean_object* v_fst_4513_; lean_object* v_fst_4514_; lean_object* v_snd_4515_; lean_object* v___y_4517_; lean_object* v_toConstantVal_4518_; lean_object* v_ctors_4519_; uint8_t v___y_4520_; lean_object* v___y_4599_; lean_object* v___x_4610_; 
v_head_4478_ = lean_ctor_get(v_as_x27_4471_, 0);
v_tail_4479_ = lean_ctor_get(v_as_x27_4471_, 1);
v_snd_4512_ = lean_ctor_get(v_b_4472_, 1);
lean_inc(v_snd_4512_);
v_fst_4513_ = lean_ctor_get(v_b_4472_, 0);
lean_inc(v_fst_4513_);
lean_dec_ref(v_b_4472_);
v_fst_4514_ = lean_ctor_get(v_snd_4512_, 0);
lean_inc(v_fst_4514_);
v_snd_4515_ = lean_ctor_get(v_snd_4512_, 1);
lean_inc(v_snd_4515_);
lean_dec(v_snd_4512_);
lean_inc(v_head_4478_);
lean_inc_ref(v___y_4473_);
v___x_4610_ = l_Lean_Environment_find_x3f(v___y_4473_, v_head_4478_, v___x_4469_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4611_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_4612_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_4611_);
v___y_4599_ = v___x_4612_;
goto v___jp_4598_;
}
else
{
lean_object* v_val_4613_; 
v_val_4613_ = lean_ctor_get(v___x_4610_, 0);
lean_inc(v_val_4613_);
lean_dec_ref_known(v___x_4610_, 1);
v___y_4599_ = v_val_4613_;
goto v___jp_4598_;
}
v___jp_4480_:
{
if (lean_obj_tag(v___y_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4503_; 
v_a_4482_ = lean_ctor_get(v___y_4481_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___y_4481_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4484_ = v___y_4481_;
v_isShared_4485_ = v_isSharedCheck_4503_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___y_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4503_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v_fst_4486_; 
v_fst_4486_ = lean_ctor_get(v_a_4482_, 0);
lean_inc(v_fst_4486_);
if (lean_obj_tag(v_fst_4486_) == 0)
{
lean_object* v_snd_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4498_; 
v_snd_4487_ = lean_ctor_get(v_a_4482_, 1);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_a_4482_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; 
v_unused_4499_ = lean_ctor_get(v_a_4482_, 0);
lean_dec(v_unused_4499_);
v___x_4489_ = v_a_4482_;
v_isShared_4490_ = v_isSharedCheck_4498_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_snd_4487_);
lean_dec(v_a_4482_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4498_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v_a_4491_; lean_object* v___x_4493_; 
v_a_4491_ = lean_ctor_get(v_fst_4486_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v_fst_4486_, 1);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v_a_4491_);
v___x_4493_ = v___x_4489_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_snd_4487_);
v___x_4493_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4495_; 
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4493_);
v___x_4495_ = v___x_4484_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
else
{
lean_object* v_snd_4500_; lean_object* v_a_4501_; 
lean_del_object(v___x_4484_);
v_snd_4500_ = lean_ctor_get(v_a_4482_, 1);
lean_inc(v_snd_4500_);
lean_dec(v_a_4482_);
v_a_4501_ = lean_ctor_get(v_fst_4486_, 0);
lean_inc(v_a_4501_);
lean_dec_ref_known(v_fst_4486_, 1);
v_as_x27_4471_ = v_tail_4479_;
v_b_4472_ = v_a_4501_;
v___y_4474_ = v_snd_4500_;
goto _start;
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
v_a_4504_ = lean_ctor_get(v___y_4481_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___y_4481_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___y_4481_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___y_4481_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
v___jp_4516_:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4521_ = lean_array_push(v_fst_4513_, v___y_4517_);
v___x_4522_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_4520_, v___x_4469_, v_ctors_4519_, v_fst_4514_, v___y_4473_, v___y_4474_);
lean_dec(v_ctors_4519_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v_snd_4524_; lean_object* v_fst_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4589_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v___x_4522_, 1);
v_snd_4524_ = lean_ctor_get(v_a_4523_, 1);
v_fst_4525_ = lean_ctor_get(v_a_4523_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v_a_4523_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4527_ = v_a_4523_;
v_isShared_4528_ = v_isSharedCheck_4589_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_snd_4524_);
lean_inc(v_fst_4525_);
lean_dec(v_a_4523_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4589_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v_visitedNames_4529_; lean_object* v_visitedLevels_4530_; lean_object* v_visitedExprs_4531_; lean_object* v_visitedConstants_4532_; lean_object* v_noMDataExprs_4533_; uint8_t v_exportMData_4534_; uint8_t v_exportUnsafe_4535_; uint8_t v_ignoreMissing_4536_; lean_object* v_recursorMap_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4588_; 
v_visitedNames_4529_ = lean_ctor_get(v_snd_4524_, 0);
v_visitedLevels_4530_ = lean_ctor_get(v_snd_4524_, 1);
v_visitedExprs_4531_ = lean_ctor_get(v_snd_4524_, 2);
v_visitedConstants_4532_ = lean_ctor_get(v_snd_4524_, 3);
v_noMDataExprs_4533_ = lean_ctor_get(v_snd_4524_, 4);
v_exportMData_4534_ = lean_ctor_get_uint8(v_snd_4524_, sizeof(void*)*6);
v_exportUnsafe_4535_ = lean_ctor_get_uint8(v_snd_4524_, sizeof(void*)*6 + 1);
v_ignoreMissing_4536_ = lean_ctor_get_uint8(v_snd_4524_, sizeof(void*)*6 + 2);
v_recursorMap_4537_ = lean_ctor_get(v_snd_4524_, 5);
v_isSharedCheck_4588_ = !lean_is_exclusive(v_snd_4524_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4539_ = v_snd_4524_;
v_isShared_4540_ = v_isSharedCheck_4588_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_recursorMap_4537_);
lean_inc(v_noMDataExprs_4533_);
lean_inc(v_visitedConstants_4532_);
lean_inc(v_visitedExprs_4531_);
lean_inc(v_visitedLevels_4530_);
lean_inc(v_visitedNames_4529_);
lean_dec(v_snd_4524_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4588_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v_type_4541_; lean_object* v___x_4542_; lean_object* v___x_4544_; 
v_type_4541_ = lean_ctor_get(v_toConstantVal_4518_, 2);
lean_inc_ref(v_type_4541_);
lean_dec_ref(v_toConstantVal_4518_);
lean_inc(v_head_4478_);
v___x_4542_ = l_Lean_NameHashSet_insert(v_visitedConstants_4532_, v_head_4478_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 3, v___x_4542_);
v___x_4544_ = v___x_4539_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_visitedNames_4529_);
lean_ctor_set(v_reuseFailAlloc_4587_, 1, v_visitedLevels_4530_);
lean_ctor_set(v_reuseFailAlloc_4587_, 2, v_visitedExprs_4531_);
lean_ctor_set(v_reuseFailAlloc_4587_, 3, v___x_4542_);
lean_ctor_set(v_reuseFailAlloc_4587_, 4, v_noMDataExprs_4533_);
lean_ctor_set(v_reuseFailAlloc_4587_, 5, v_recursorMap_4537_);
lean_ctor_set_uint8(v_reuseFailAlloc_4587_, sizeof(void*)*6, v_exportMData_4534_);
lean_ctor_set_uint8(v_reuseFailAlloc_4587_, sizeof(void*)*6 + 1, v_exportUnsafe_4535_);
lean_ctor_set_uint8(v_reuseFailAlloc_4587_, sizeof(void*)*6 + 2, v_ignoreMissing_4536_);
v___x_4544_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
lean_object* v___x_4545_; 
v___x_4545_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4541_, v___y_4473_, v___x_4544_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; lean_object* v_snd_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4577_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc(v_a_4546_);
lean_dec_ref_known(v___x_4545_, 1);
v_snd_4547_ = lean_ctor_get(v_a_4546_, 1);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_a_4546_);
if (v_isSharedCheck_4577_ == 0)
{
lean_object* v_unused_4578_; 
v_unused_4578_ = lean_ctor_get(v_a_4546_, 0);
lean_dec(v_unused_4578_);
v___x_4549_ = v_a_4546_;
v_isShared_4550_ = v_isSharedCheck_4577_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_snd_4547_);
lean_dec(v_a_4546_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4577_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v_toConstantVal_4551_; lean_object* v_recursorMap_4552_; lean_object* v_name_4553_; lean_object* v___x_4554_; 
v_toConstantVal_4551_ = lean_ctor_get(v_val_4470_, 0);
v_recursorMap_4552_ = lean_ctor_get(v_snd_4547_, 5);
v_name_4553_ = lean_ctor_get(v_toConstantVal_4551_, 0);
v___x_4554_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_recursorMap_4552_, v_name_4553_);
if (lean_obj_tag(v___x_4554_) == 1)
{
lean_object* v_val_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4559_; 
v_val_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_val_4555_);
lean_dec_ref_known(v___x_4554_, 1);
v___x_4556_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0));
v___x_4557_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v___x_4556_, v_snd_4515_, v_val_4555_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 1, v___x_4557_);
lean_ctor_set(v___x_4549_, 0, v_fst_4525_);
v___x_4559_ = v___x_4549_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_fst_4525_);
lean_ctor_set(v_reuseFailAlloc_4564_, 1, v___x_4557_);
v___x_4559_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
lean_object* v___x_4561_; 
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 1, v___x_4559_);
lean_ctor_set(v___x_4527_, 0, v___x_4521_);
v___x_4561_ = v___x_4527_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4563_, 1, v___x_4559_);
v___x_4561_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
v_as_x27_4471_ = v_tail_4479_;
v_b_4472_ = v___x_4561_;
v___y_4474_ = v_snd_4547_;
goto _start;
}
}
}
else
{
lean_object* v___x_4565_; lean_object* v___x_4566_; uint8_t v___x_4567_; 
lean_dec(v___x_4554_);
v___x_4565_ = lean_array_get_size(v_fst_4525_);
v___x_4566_ = lean_unsigned_to_nat(0u);
v___x_4567_ = lean_nat_dec_eq(v___x_4565_, v___x_4566_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
lean_del_object(v___x_4549_);
lean_del_object(v___x_4527_);
lean_dec(v_fst_4525_);
lean_dec_ref(v___x_4521_);
lean_dec(v_snd_4515_);
v___x_4568_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2);
v___x_4569_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4568_, v___y_4473_, v_snd_4547_);
v___y_4481_ = v___x_4569_;
goto v___jp_4480_;
}
else
{
lean_object* v___x_4571_; 
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 1, v_snd_4515_);
lean_ctor_set(v___x_4549_, 0, v_fst_4525_);
v___x_4571_ = v___x_4549_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_fst_4525_);
lean_ctor_set(v_reuseFailAlloc_4576_, 1, v_snd_4515_);
v___x_4571_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
lean_object* v___x_4573_; 
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 1, v___x_4571_);
lean_ctor_set(v___x_4527_, 0, v___x_4521_);
v___x_4573_ = v___x_4527_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4575_, 1, v___x_4571_);
v___x_4573_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
v_as_x27_4471_ = v_tail_4479_;
v_b_4472_ = v___x_4573_;
v___y_4474_ = v_snd_4547_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_del_object(v___x_4527_);
lean_dec(v_fst_4525_);
lean_dec_ref(v___x_4521_);
lean_dec(v_snd_4515_);
v_a_4579_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4545_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4545_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4597_; 
lean_dec_ref(v___x_4521_);
lean_dec_ref(v_toConstantVal_4518_);
lean_dec(v_snd_4515_);
v_a_4590_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4592_ = v___x_4522_;
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4522_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
v___jp_4598_:
{
lean_object* v___x_4600_; uint8_t v_isUnsafe_4601_; 
v___x_4600_ = l_Lean_ConstantInfo_inductiveVal_x21(v___y_4599_);
lean_dec_ref(v___y_4599_);
v_isUnsafe_4601_ = lean_ctor_get_uint8(v___x_4600_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4601_ == 0)
{
lean_object* v_toConstantVal_4602_; lean_object* v_ctors_4603_; uint8_t v___x_4604_; 
v_toConstantVal_4602_ = lean_ctor_get(v___x_4600_, 0);
lean_inc_ref(v_toConstantVal_4602_);
v_ctors_4603_ = lean_ctor_get(v___x_4600_, 4);
lean_inc(v_ctors_4603_);
v___x_4604_ = 1;
v___y_4517_ = v___x_4600_;
v_toConstantVal_4518_ = v_toConstantVal_4602_;
v_ctors_4519_ = v_ctors_4603_;
v___y_4520_ = v___x_4604_;
goto v___jp_4516_;
}
else
{
uint8_t v_exportUnsafe_4605_; 
v_exportUnsafe_4605_ = lean_ctor_get_uint8(v___y_4474_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_4605_ == 0)
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
lean_dec_ref(v___x_4600_);
lean_dec(v_snd_4515_);
lean_dec(v_fst_4514_);
lean_dec(v_fst_4513_);
v___x_4606_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4);
v___x_4607_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4606_, v___y_4473_, v___y_4474_);
v___y_4481_ = v___x_4607_;
goto v___jp_4480_;
}
else
{
lean_object* v_toConstantVal_4608_; lean_object* v_ctors_4609_; 
v_toConstantVal_4608_ = lean_ctor_get(v___x_4600_, 0);
lean_inc_ref(v_toConstantVal_4608_);
v_ctors_4609_ = lean_ctor_get(v___x_4600_, 4);
lean_inc(v_ctors_4609_);
v___y_4517_ = v___x_4600_;
v_toConstantVal_4518_ = v_toConstantVal_4608_;
v_ctors_4519_ = v_ctors_4609_;
v___y_4520_ = v_exportUnsafe_4605_;
goto v___jp_4516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(lean_object* v_as_4614_, size_t v_sz_4615_, size_t v_i_4616_, lean_object* v_b_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
uint8_t v___x_4621_; 
v___x_4621_ = lean_usize_dec_lt(v_i_4616_, v_sz_4615_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4622_, 0, v_b_4617_);
lean_ctor_set(v___x_4622_, 1, v___y_4619_);
v___x_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
return v___x_4623_;
}
else
{
lean_object* v_visitedNames_4624_; lean_object* v_visitedLevels_4625_; lean_object* v_visitedExprs_4626_; lean_object* v_visitedConstants_4627_; lean_object* v_noMDataExprs_4628_; uint8_t v_exportMData_4629_; uint8_t v_exportUnsafe_4630_; uint8_t v_ignoreMissing_4631_; lean_object* v_recursorMap_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4651_; 
v_visitedNames_4624_ = lean_ctor_get(v___y_4619_, 0);
v_visitedLevels_4625_ = lean_ctor_get(v___y_4619_, 1);
v_visitedExprs_4626_ = lean_ctor_get(v___y_4619_, 2);
v_visitedConstants_4627_ = lean_ctor_get(v___y_4619_, 3);
v_noMDataExprs_4628_ = lean_ctor_get(v___y_4619_, 4);
v_exportMData_4629_ = lean_ctor_get_uint8(v___y_4619_, sizeof(void*)*6);
v_exportUnsafe_4630_ = lean_ctor_get_uint8(v___y_4619_, sizeof(void*)*6 + 1);
v_ignoreMissing_4631_ = lean_ctor_get_uint8(v___y_4619_, sizeof(void*)*6 + 2);
v_recursorMap_4632_ = lean_ctor_get(v___y_4619_, 5);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___y_4619_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4634_ = v___y_4619_;
v_isShared_4635_ = v_isSharedCheck_4651_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_recursorMap_4632_);
lean_inc(v_noMDataExprs_4628_);
lean_inc(v_visitedConstants_4627_);
lean_inc(v_visitedExprs_4626_);
lean_inc(v_visitedLevels_4625_);
lean_inc(v_visitedNames_4624_);
lean_dec(v___y_4619_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4651_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v_a_4636_; lean_object* v_toConstantVal_4637_; lean_object* v_name_4638_; lean_object* v_type_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4643_; 
v_a_4636_ = lean_array_uget_borrowed(v_as_4614_, v_i_4616_);
v_toConstantVal_4637_ = lean_ctor_get(v_a_4636_, 0);
v_name_4638_ = lean_ctor_get(v_toConstantVal_4637_, 0);
v_type_4639_ = lean_ctor_get(v_toConstantVal_4637_, 2);
v___x_4640_ = lean_box(0);
lean_inc(v_name_4638_);
v___x_4641_ = l_Lean_NameHashSet_insert(v_visitedConstants_4627_, v_name_4638_);
if (v_isShared_4635_ == 0)
{
lean_ctor_set(v___x_4634_, 3, v___x_4641_);
v___x_4643_ = v___x_4634_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_visitedNames_4624_);
lean_ctor_set(v_reuseFailAlloc_4650_, 1, v_visitedLevels_4625_);
lean_ctor_set(v_reuseFailAlloc_4650_, 2, v_visitedExprs_4626_);
lean_ctor_set(v_reuseFailAlloc_4650_, 3, v___x_4641_);
lean_ctor_set(v_reuseFailAlloc_4650_, 4, v_noMDataExprs_4628_);
lean_ctor_set(v_reuseFailAlloc_4650_, 5, v_recursorMap_4632_);
lean_ctor_set_uint8(v_reuseFailAlloc_4650_, sizeof(void*)*6, v_exportMData_4629_);
lean_ctor_set_uint8(v_reuseFailAlloc_4650_, sizeof(void*)*6 + 1, v_exportUnsafe_4630_);
lean_ctor_set_uint8(v_reuseFailAlloc_4650_, sizeof(void*)*6 + 2, v_ignoreMissing_4631_);
v___x_4643_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
lean_object* v___x_4644_; 
lean_inc_ref(v_type_4639_);
v___x_4644_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4639_, v___y_4618_, v___x_4643_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v_snd_4646_; size_t v___x_4647_; size_t v___x_4648_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v___x_4644_, 1);
v_snd_4646_ = lean_ctor_get(v_a_4645_, 1);
lean_inc(v_snd_4646_);
lean_dec(v_a_4645_);
v___x_4647_ = ((size_t)1ULL);
v___x_4648_ = lean_usize_add(v_i_4616_, v___x_4647_);
v_i_4616_ = v___x_4648_;
v_b_4617_ = v___x_4640_;
v___y_4619_ = v_snd_4646_;
goto _start;
}
else
{
return v___x_4644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(lean_object* v_as_x27_4652_, lean_object* v_b_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
if (lean_obj_tag(v_as_x27_4652_) == 0)
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4657_, 0, v_b_4653_);
lean_ctor_set(v___x_4657_, 1, v___y_4655_);
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
return v___x_4658_;
}
else
{
lean_object* v_head_4659_; lean_object* v_tail_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v_head_4659_ = lean_ctor_get(v_as_x27_4652_, 0);
v_tail_4660_ = lean_ctor_get(v_as_x27_4652_, 1);
v___x_4661_ = lean_box(0);
lean_inc(v_head_4659_);
v___x_4662_ = l_LeanExport_dumpConstant(v_head_4659_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v_snd_4664_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref_known(v___x_4662_, 1);
v_snd_4664_ = lean_ctor_get(v_a_4663_, 1);
lean_inc(v_snd_4664_);
lean_dec(v_a_4663_);
v_as_x27_4652_ = v_tail_4660_;
v_b_4653_ = v___x_4661_;
v___y_4655_ = v_snd_4664_;
goto _start;
}
else
{
return v___x_4662_;
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant(lean_object* v_c_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v___y_4675_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v_fst_4678_; lean_object* v_snd_4679_; uint8_t v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = 0;
lean_inc(v_c_4666_);
lean_inc_ref(v_a_4667_);
v___x_4777_ = l_Lean_Environment_find_x3f(v_a_4667_, v_c_4666_, v___x_4776_);
if (lean_obj_tag(v___x_4777_) == 1)
{
lean_object* v_val_4778_; uint8_t v___x_5516_; 
v_val_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_val_4778_);
lean_dec_ref_known(v___x_4777_, 1);
v___x_5516_ = l_Lean_ConstantInfo_isUnsafe(v_val_4778_);
if (v___x_5516_ == 0)
{
goto v___jp_4779_;
}
else
{
uint8_t v_exportUnsafe_5517_; 
v_exportUnsafe_5517_ = lean_ctor_get_uint8(v_a_4668_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_5517_ == 0)
{
lean_dec(v_val_4778_);
lean_dec(v_c_4666_);
goto v___jp_4670_;
}
else
{
goto v___jp_4779_;
}
}
v___jp_4779_:
{
lean_object* v_visitedNames_4780_; lean_object* v_visitedLevels_4781_; lean_object* v_visitedExprs_4782_; lean_object* v_visitedConstants_4783_; lean_object* v_noMDataExprs_4784_; uint8_t v_exportMData_4785_; uint8_t v_exportUnsafe_4786_; uint8_t v_ignoreMissing_4787_; lean_object* v_recursorMap_4788_; uint8_t v___x_4789_; 
v_visitedNames_4780_ = lean_ctor_get(v_a_4668_, 0);
v_visitedLevels_4781_ = lean_ctor_get(v_a_4668_, 1);
v_visitedExprs_4782_ = lean_ctor_get(v_a_4668_, 2);
v_visitedConstants_4783_ = lean_ctor_get(v_a_4668_, 3);
v_noMDataExprs_4784_ = lean_ctor_get(v_a_4668_, 4);
v_exportMData_4785_ = lean_ctor_get_uint8(v_a_4668_, sizeof(void*)*6);
v_exportUnsafe_4786_ = lean_ctor_get_uint8(v_a_4668_, sizeof(void*)*6 + 1);
v_ignoreMissing_4787_ = lean_ctor_get_uint8(v_a_4668_, sizeof(void*)*6 + 2);
v_recursorMap_4788_ = lean_ctor_get(v_a_4668_, 5);
v___x_4789_ = l_Lean_NameHashSet_contains(v_visitedConstants_4783_, v_c_4666_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_5509_; 
lean_inc(v_recursorMap_4788_);
lean_inc_ref(v_noMDataExprs_4784_);
lean_inc_ref(v_visitedConstants_4783_);
lean_inc_ref(v_visitedExprs_4782_);
lean_inc_ref(v_visitedLevels_4781_);
lean_inc_ref(v_visitedNames_4780_);
v_isSharedCheck_5509_ = !lean_is_exclusive(v_a_4668_);
if (v_isSharedCheck_5509_ == 0)
{
lean_object* v_unused_5510_; lean_object* v_unused_5511_; lean_object* v_unused_5512_; lean_object* v_unused_5513_; lean_object* v_unused_5514_; lean_object* v_unused_5515_; 
v_unused_5510_ = lean_ctor_get(v_a_4668_, 5);
lean_dec(v_unused_5510_);
v_unused_5511_ = lean_ctor_get(v_a_4668_, 4);
lean_dec(v_unused_5511_);
v_unused_5512_ = lean_ctor_get(v_a_4668_, 3);
lean_dec(v_unused_5512_);
v_unused_5513_ = lean_ctor_get(v_a_4668_, 2);
lean_dec(v_unused_5513_);
v_unused_5514_ = lean_ctor_get(v_a_4668_, 1);
lean_dec(v_unused_5514_);
v_unused_5515_ = lean_ctor_get(v_a_4668_, 0);
lean_dec(v_unused_5515_);
v___x_4791_ = v_a_4668_;
v_isShared_4792_ = v_isSharedCheck_5509_;
goto v_resetjp_4790_;
}
else
{
lean_dec(v_a_4668_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_5509_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4793_; lean_object* v___x_4795_; 
v___x_4793_ = l_Lean_NameHashSet_insert(v_visitedConstants_4783_, v_c_4666_);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 3, v___x_4793_);
v___x_4795_ = v___x_4791_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_visitedNames_4780_);
lean_ctor_set(v_reuseFailAlloc_5508_, 1, v_visitedLevels_4781_);
lean_ctor_set(v_reuseFailAlloc_5508_, 2, v_visitedExprs_4782_);
lean_ctor_set(v_reuseFailAlloc_5508_, 3, v___x_4793_);
lean_ctor_set(v_reuseFailAlloc_5508_, 4, v_noMDataExprs_4784_);
lean_ctor_set(v_reuseFailAlloc_5508_, 5, v_recursorMap_4788_);
lean_ctor_set_uint8(v_reuseFailAlloc_5508_, sizeof(void*)*6, v_exportMData_4785_);
lean_ctor_set_uint8(v_reuseFailAlloc_5508_, sizeof(void*)*6 + 1, v_exportUnsafe_4786_);
lean_ctor_set_uint8(v_reuseFailAlloc_5508_, sizeof(void*)*6 + 2, v_ignoreMissing_4787_);
v___x_4795_ = v_reuseFailAlloc_5508_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
switch(lean_obj_tag(v_val_4778_))
{
case 0:
{
lean_object* v_val_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4900_; 
v_val_4796_ = lean_ctor_get(v_val_4778_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v_val_4778_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4798_ = v_val_4778_;
v_isShared_4799_ = v_isSharedCheck_4900_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_val_4796_);
lean_dec(v_val_4778_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4900_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v_toConstantVal_4800_; uint8_t v_isUnsafe_4801_; lean_object* v_name_4802_; lean_object* v_levelParams_4803_; lean_object* v_type_4804_; lean_object* v___x_4805_; 
v_toConstantVal_4800_ = lean_ctor_get(v_val_4796_, 0);
lean_inc_ref(v_toConstantVal_4800_);
v_isUnsafe_4801_ = lean_ctor_get_uint8(v_val_4796_, sizeof(void*)*1);
lean_dec_ref(v_val_4796_);
v_name_4802_ = lean_ctor_get(v_toConstantVal_4800_, 0);
lean_inc(v_name_4802_);
v_levelParams_4803_ = lean_ctor_get(v_toConstantVal_4800_, 1);
lean_inc(v_levelParams_4803_);
v_type_4804_ = lean_ctor_get(v_toConstantVal_4800_, 2);
lean_inc_ref_n(v_type_4804_, 2);
lean_dec_ref(v_toConstantVal_4800_);
v___x_4805_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4804_, v_a_4667_, v___x_4795_);
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4899_; 
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4808_ = v___x_4805_;
v_isShared_4809_ = v_isSharedCheck_4899_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4805_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4899_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v_snd_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4897_; 
v_snd_4810_ = lean_ctor_get(v_a_4806_, 1);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_a_4806_);
if (v_isSharedCheck_4897_ == 0)
{
lean_object* v_unused_4898_; 
v_unused_4898_ = lean_ctor_get(v_a_4806_, 0);
lean_dec(v_unused_4898_);
v___x_4812_ = v_a_4806_;
v_isShared_4813_ = v_isSharedCheck_4897_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_snd_4810_);
lean_dec(v_a_4806_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4897_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4814_; 
v___x_4814_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4802_, v_a_4667_, v_snd_4810_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v_a_4815_; lean_object* v_fst_4816_; lean_object* v_snd_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4888_; 
v_a_4815_ = lean_ctor_get(v___x_4814_, 0);
lean_inc(v_a_4815_);
lean_dec_ref_known(v___x_4814_, 1);
v_fst_4816_ = lean_ctor_get(v_a_4815_, 0);
v_snd_4817_ = lean_ctor_get(v_a_4815_, 1);
v_isSharedCheck_4888_ = !lean_is_exclusive(v_a_4815_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4819_ = v_a_4815_;
v_isShared_4820_ = v_isSharedCheck_4888_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_snd_4817_);
lean_inc(v_fst_4816_);
lean_dec(v_a_4815_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4888_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; 
v___x_4821_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4803_, v_a_4667_, v_snd_4817_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v_fst_4823_; lean_object* v_snd_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4879_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___x_4821_, 1);
v_fst_4823_ = lean_ctor_get(v_a_4822_, 0);
v_snd_4824_ = lean_ctor_get(v_a_4822_, 1);
v_isSharedCheck_4879_ = !lean_is_exclusive(v_a_4822_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4826_ = v_a_4822_;
v_isShared_4827_ = v_isSharedCheck_4879_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_snd_4824_);
lean_inc(v_fst_4823_);
lean_dec(v_a_4822_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4879_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4828_; 
v___x_4828_ = l_LeanExport_dumpExpr(v_type_4804_, v_a_4667_, v_snd_4824_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v_fst_4830_; lean_object* v_snd_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4870_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref_known(v___x_4828_, 1);
v_fst_4830_ = lean_ctor_get(v_a_4829_, 0);
v_snd_4831_ = lean_ctor_get(v_a_4829_, 1);
v_isSharedCheck_4870_ = !lean_is_exclusive(v_a_4829_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4833_ = v_a_4829_;
v_isShared_4834_ = v_isSharedCheck_4870_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_snd_4831_);
lean_inc(v_fst_4830_);
lean_dec(v_a_4829_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4870_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4839_; 
v___x_4835_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__3));
v___x_4836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4837_ = l_Lean_JsonNumber_fromNat(v_fst_4816_);
if (v_isShared_4809_ == 0)
{
lean_ctor_set_tag(v___x_4808_, 2);
lean_ctor_set(v___x_4808_, 0, v___x_4837_);
v___x_4839_ = v___x_4808_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4837_);
v___x_4839_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
lean_object* v___x_4841_; 
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 1, v___x_4839_);
lean_ctor_set(v___x_4833_, 0, v___x_4836_);
v___x_4841_ = v___x_4833_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4836_);
lean_ctor_set(v_reuseFailAlloc_4868_, 1, v___x_4839_);
v___x_4841_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
lean_object* v___x_4842_; lean_object* v___x_4844_; 
v___x_4842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 1, v_fst_4823_);
lean_ctor_set(v___x_4826_, 0, v___x_4842_);
v___x_4844_ = v___x_4826_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4842_);
lean_ctor_set(v_reuseFailAlloc_4867_, 1, v_fst_4823_);
v___x_4844_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4848_; 
v___x_4845_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4846_ = l_Lean_JsonNumber_fromNat(v_fst_4830_);
if (v_isShared_4799_ == 0)
{
lean_ctor_set_tag(v___x_4798_, 2);
lean_ctor_set(v___x_4798_, 0, v___x_4846_);
v___x_4848_ = v___x_4798_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4846_);
v___x_4848_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
lean_object* v___x_4850_; 
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 1, v___x_4848_);
lean_ctor_set(v___x_4819_, 0, v___x_4845_);
v___x_4850_ = v___x_4819_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v___x_4845_);
lean_ctor_set(v_reuseFailAlloc_4865_, 1, v___x_4848_);
v___x_4850_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4854_; 
v___x_4851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_4852_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4852_, 0, v_isUnsafe_4801_);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 1, v___x_4852_);
lean_ctor_set(v___x_4812_, 0, v___x_4851_);
v___x_4854_ = v___x_4812_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v___x_4851_);
lean_ctor_set(v_reuseFailAlloc_4864_, 1, v___x_4852_);
v___x_4854_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4855_ = lean_box(0);
v___x_4856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4854_);
lean_ctor_set(v___x_4856_, 1, v___x_4855_);
v___x_4857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4850_);
lean_ctor_set(v___x_4857_, 1, v___x_4856_);
v___x_4858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4844_);
lean_ctor_set(v___x_4858_, 1, v___x_4857_);
v___x_4859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4841_);
lean_ctor_set(v___x_4859_, 1, v___x_4858_);
v___x_4860_ = l_Lean_Json_mkObj(v___x_4859_);
lean_dec_ref_known(v___x_4859_, 2);
v___x_4861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4835_);
lean_ctor_set(v___x_4861_, 1, v___x_4860_);
v___x_4862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
lean_ctor_set(v___x_4862_, 1, v___x_4855_);
v___x_4863_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4862_, v_snd_4831_);
lean_dec_ref_known(v___x_4862_, 2);
return v___x_4863_;
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
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4878_; 
lean_del_object(v___x_4826_);
lean_dec(v_fst_4823_);
lean_del_object(v___x_4819_);
lean_dec(v_fst_4816_);
lean_del_object(v___x_4812_);
lean_del_object(v___x_4808_);
lean_del_object(v___x_4798_);
v_a_4871_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4873_ = v___x_4828_;
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4828_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4876_; 
if (v_isShared_4874_ == 0)
{
v___x_4876_ = v___x_4873_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
lean_del_object(v___x_4819_);
lean_dec(v_fst_4816_);
lean_del_object(v___x_4812_);
lean_del_object(v___x_4808_);
lean_dec_ref(v_type_4804_);
lean_del_object(v___x_4798_);
v_a_4880_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4821_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4821_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
lean_del_object(v___x_4812_);
lean_del_object(v___x_4808_);
lean_dec_ref(v_type_4804_);
lean_dec(v_levelParams_4803_);
lean_del_object(v___x_4798_);
v_a_4889_ = lean_ctor_get(v___x_4814_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4814_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4814_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4814_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_type_4804_);
lean_dec(v_levelParams_4803_);
lean_dec(v_name_4802_);
lean_del_object(v___x_4798_);
return v___x_4805_;
}
}
}
case 1:
{
lean_object* v_val_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_5072_; 
v_val_4901_ = lean_ctor_get(v_val_4778_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v_val_4778_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_4903_ = v_val_4778_;
v_isShared_4904_ = v_isSharedCheck_5072_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_val_4901_);
lean_dec(v_val_4778_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_5072_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v_toConstantVal_4905_; lean_object* v_value_4906_; lean_object* v_hints_4907_; uint8_t v_safety_4908_; lean_object* v_all_4909_; lean_object* v_name_4910_; lean_object* v_levelParams_4911_; lean_object* v_type_4912_; lean_object* v___x_4913_; 
v_toConstantVal_4905_ = lean_ctor_get(v_val_4901_, 0);
lean_inc_ref(v_toConstantVal_4905_);
v_value_4906_ = lean_ctor_get(v_val_4901_, 1);
lean_inc_ref(v_value_4906_);
v_hints_4907_ = lean_ctor_get(v_val_4901_, 2);
lean_inc(v_hints_4907_);
v_safety_4908_ = lean_ctor_get_uint8(v_val_4901_, sizeof(void*)*4);
v_all_4909_ = lean_ctor_get(v_val_4901_, 3);
lean_inc(v_all_4909_);
lean_dec_ref(v_val_4901_);
v_name_4910_ = lean_ctor_get(v_toConstantVal_4905_, 0);
lean_inc(v_name_4910_);
v_levelParams_4911_ = lean_ctor_get(v_toConstantVal_4905_, 1);
lean_inc(v_levelParams_4911_);
v_type_4912_ = lean_ctor_get(v_toConstantVal_4905_, 2);
lean_inc_ref_n(v_type_4912_, 2);
lean_dec_ref(v_toConstantVal_4905_);
v___x_4913_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4912_, v_a_4667_, v___x_4795_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_5071_; 
v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_4916_ = v___x_4913_;
v_isShared_4917_ = v_isSharedCheck_5071_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4913_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_5071_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v_snd_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_5069_; 
v_snd_4918_ = lean_ctor_get(v_a_4914_, 1);
v_isSharedCheck_5069_ = !lean_is_exclusive(v_a_4914_);
if (v_isSharedCheck_5069_ == 0)
{
lean_object* v_unused_5070_; 
v_unused_5070_ = lean_ctor_get(v_a_4914_, 0);
lean_dec(v_unused_5070_);
v___x_4920_ = v_a_4914_;
v_isShared_4921_ = v_isSharedCheck_5069_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_snd_4918_);
lean_dec(v_a_4914_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_5069_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4922_; 
lean_inc_ref(v_value_4906_);
v___x_4922_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_4906_, v_a_4667_, v_snd_4918_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_5068_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_4925_ = v___x_4922_;
v_isShared_4926_ = v_isSharedCheck_5068_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4922_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_5068_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v_snd_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_5066_; 
v_snd_4927_ = lean_ctor_get(v_a_4923_, 1);
v_isSharedCheck_5066_ = !lean_is_exclusive(v_a_4923_);
if (v_isSharedCheck_5066_ == 0)
{
lean_object* v_unused_5067_; 
v_unused_5067_ = lean_ctor_get(v_a_4923_, 0);
lean_dec(v_unused_5067_);
v___x_4929_ = v_a_4923_;
v_isShared_4930_ = v_isSharedCheck_5066_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_snd_4927_);
lean_dec(v_a_4923_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_5066_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4931_; 
v___x_4931_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4910_, v_a_4667_, v_snd_4927_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v_a_4932_; lean_object* v_fst_4933_; lean_object* v_snd_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_5057_; 
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc(v_a_4932_);
lean_dec_ref_known(v___x_4931_, 1);
v_fst_4933_ = lean_ctor_get(v_a_4932_, 0);
v_snd_4934_ = lean_ctor_get(v_a_4932_, 1);
v_isSharedCheck_5057_ = !lean_is_exclusive(v_a_4932_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_4936_ = v_a_4932_;
v_isShared_4937_ = v_isSharedCheck_5057_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_snd_4934_);
lean_inc(v_fst_4933_);
lean_dec(v_a_4932_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_5057_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4938_; 
v___x_4938_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4911_, v_a_4667_, v_snd_4934_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v_fst_4940_; lean_object* v_snd_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_5048_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___x_4938_, 1);
v_fst_4940_ = lean_ctor_get(v_a_4939_, 0);
v_snd_4941_ = lean_ctor_get(v_a_4939_, 1);
v_isSharedCheck_5048_ = !lean_is_exclusive(v_a_4939_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_4943_ = v_a_4939_;
v_isShared_4944_ = v_isSharedCheck_5048_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_snd_4941_);
lean_inc(v_fst_4940_);
lean_dec(v_a_4939_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_5048_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4945_; 
v___x_4945_ = l_LeanExport_dumpExpr(v_type_4912_, v_a_4667_, v_snd_4941_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v_a_4946_; lean_object* v_fst_4947_; lean_object* v_snd_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_5039_; 
v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
lean_inc(v_a_4946_);
lean_dec_ref_known(v___x_4945_, 1);
v_fst_4947_ = lean_ctor_get(v_a_4946_, 0);
v_snd_4948_ = lean_ctor_get(v_a_4946_, 1);
v_isSharedCheck_5039_ = !lean_is_exclusive(v_a_4946_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_4950_ = v_a_4946_;
v_isShared_4951_ = v_isSharedCheck_5039_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_snd_4948_);
lean_inc(v_fst_4947_);
lean_dec(v_a_4946_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_5039_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4952_; 
v___x_4952_ = l_LeanExport_dumpExpr(v_value_4906_, v_a_4667_, v_snd_4948_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v_a_4953_; lean_object* v_fst_4954_; lean_object* v_snd_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_5030_; 
v_a_4953_ = lean_ctor_get(v___x_4952_, 0);
lean_inc(v_a_4953_);
lean_dec_ref_known(v___x_4952_, 1);
v_fst_4954_ = lean_ctor_get(v_a_4953_, 0);
v_snd_4955_ = lean_ctor_get(v_a_4953_, 1);
v_isSharedCheck_5030_ = !lean_is_exclusive(v_a_4953_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_4957_ = v_a_4953_;
v_isShared_4958_ = v_isSharedCheck_5030_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_snd_4955_);
lean_inc(v_fst_4954_);
lean_dec(v_a_4953_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_5030_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4959_; 
v___x_4959_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_4909_, v_a_4667_, v_snd_4955_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v_a_4960_; lean_object* v_fst_4961_; lean_object* v_snd_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_5021_; 
v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
lean_inc(v_a_4960_);
lean_dec_ref_known(v___x_4959_, 1);
v_fst_4961_ = lean_ctor_get(v_a_4960_, 0);
v_snd_4962_ = lean_ctor_get(v_a_4960_, 1);
v_isSharedCheck_5021_ = !lean_is_exclusive(v_a_4960_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_4964_ = v_a_4960_;
v_isShared_4965_ = v_isSharedCheck_5021_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_snd_4962_);
lean_inc(v_fst_4961_);
lean_dec(v_a_4960_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_5021_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4970_; 
v___x_4966_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__4));
v___x_4967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4968_ = l_Lean_JsonNumber_fromNat(v_fst_4933_);
if (v_isShared_4926_ == 0)
{
lean_ctor_set_tag(v___x_4925_, 2);
lean_ctor_set(v___x_4925_, 0, v___x_4968_);
v___x_4970_ = v___x_4925_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v___x_4968_);
v___x_4970_ = v_reuseFailAlloc_5020_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4972_; 
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 1, v___x_4970_);
lean_ctor_set(v___x_4964_, 0, v___x_4967_);
v___x_4972_ = v___x_4964_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___x_4967_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v___x_4970_);
v___x_4972_ = v_reuseFailAlloc_5019_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
lean_object* v___x_4973_; lean_object* v___x_4975_; 
v___x_4973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 1, v_fst_4940_);
lean_ctor_set(v___x_4957_, 0, v___x_4973_);
v___x_4975_ = v___x_4957_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_4973_);
lean_ctor_set(v_reuseFailAlloc_5018_, 1, v_fst_4940_);
v___x_4975_ = v_reuseFailAlloc_5018_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4979_; 
v___x_4976_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4977_ = l_Lean_JsonNumber_fromNat(v_fst_4947_);
if (v_isShared_4917_ == 0)
{
lean_ctor_set_tag(v___x_4916_, 2);
lean_ctor_set(v___x_4916_, 0, v___x_4977_);
v___x_4979_ = v___x_4916_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_4977_);
v___x_4979_ = v_reuseFailAlloc_5017_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
lean_object* v___x_4981_; 
if (v_isShared_4951_ == 0)
{
lean_ctor_set(v___x_4950_, 1, v___x_4979_);
lean_ctor_set(v___x_4950_, 0, v___x_4976_);
v___x_4981_ = v___x_4950_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_4976_);
lean_ctor_set(v_reuseFailAlloc_5016_, 1, v___x_4979_);
v___x_4981_ = v_reuseFailAlloc_5016_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4985_; 
v___x_4982_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_4983_ = l_Lean_JsonNumber_fromNat(v_fst_4954_);
if (v_isShared_4904_ == 0)
{
lean_ctor_set_tag(v___x_4903_, 2);
lean_ctor_set(v___x_4903_, 0, v___x_4983_);
v___x_4985_ = v___x_4903_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v___x_4983_);
v___x_4985_ = v_reuseFailAlloc_5015_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
lean_object* v___x_4987_; 
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 1, v___x_4985_);
lean_ctor_set(v___x_4943_, 0, v___x_4982_);
v___x_4987_ = v___x_4943_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_4982_);
lean_ctor_set(v_reuseFailAlloc_5014_, 1, v___x_4985_);
v___x_4987_ = v_reuseFailAlloc_5014_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4991_; 
v___x_4988_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__5));
v___x_4989_ = l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(v_hints_4907_);
lean_dec(v_hints_4907_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 1, v___x_4989_);
lean_ctor_set(v___x_4936_, 0, v___x_4988_);
v___x_4991_ = v___x_4936_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_4988_);
lean_ctor_set(v_reuseFailAlloc_5013_, 1, v___x_4989_);
v___x_4991_ = v_reuseFailAlloc_5013_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4995_; 
v___x_4992_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__6));
v___x_4993_ = l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(v_safety_4908_);
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 1, v___x_4993_);
lean_ctor_set(v___x_4929_, 0, v___x_4992_);
v___x_4995_ = v___x_4929_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v___x_4992_);
lean_ctor_set(v_reuseFailAlloc_5012_, 1, v___x_4993_);
v___x_4995_ = v_reuseFailAlloc_5012_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
lean_object* v___x_4996_; lean_object* v___x_4998_; 
v___x_4996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 1, v_fst_4961_);
lean_ctor_set(v___x_4920_, 0, v___x_4996_);
v___x_4998_ = v___x_4920_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v___x_4996_);
lean_ctor_set(v_reuseFailAlloc_5011_, 1, v_fst_4961_);
v___x_4998_ = v_reuseFailAlloc_5011_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_4999_ = lean_box(0);
v___x_5000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4998_);
lean_ctor_set(v___x_5000_, 1, v___x_4999_);
v___x_5001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5001_, 0, v___x_4995_);
lean_ctor_set(v___x_5001_, 1, v___x_5000_);
v___x_5002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___x_4991_);
lean_ctor_set(v___x_5002_, 1, v___x_5001_);
v___x_5003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5003_, 0, v___x_4987_);
lean_ctor_set(v___x_5003_, 1, v___x_5002_);
v___x_5004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5004_, 0, v___x_4981_);
lean_ctor_set(v___x_5004_, 1, v___x_5003_);
v___x_5005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5005_, 0, v___x_4975_);
lean_ctor_set(v___x_5005_, 1, v___x_5004_);
v___x_5006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5006_, 0, v___x_4972_);
lean_ctor_set(v___x_5006_, 1, v___x_5005_);
v___x_5007_ = l_Lean_Json_mkObj(v___x_5006_);
lean_dec_ref_known(v___x_5006_, 2);
v___x_5008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5008_, 0, v___x_4966_);
lean_ctor_set(v___x_5008_, 1, v___x_5007_);
v___x_5009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5008_);
lean_ctor_set(v___x_5009_, 1, v___x_4999_);
v___x_5010_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5009_, v_snd_4962_);
lean_dec_ref_known(v___x_5009_, 2);
return v___x_5010_;
}
}
}
}
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
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
lean_del_object(v___x_4957_);
lean_dec(v_fst_4954_);
lean_del_object(v___x_4950_);
lean_dec(v_fst_4947_);
lean_del_object(v___x_4943_);
lean_dec(v_fst_4940_);
lean_del_object(v___x_4936_);
lean_dec(v_fst_4933_);
lean_del_object(v___x_4929_);
lean_del_object(v___x_4925_);
lean_del_object(v___x_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_hints_4907_);
lean_del_object(v___x_4903_);
v_a_5022_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v___x_4959_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_4959_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
}
}
else
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5038_; 
lean_del_object(v___x_4950_);
lean_dec(v_fst_4947_);
lean_del_object(v___x_4943_);
lean_dec(v_fst_4940_);
lean_del_object(v___x_4936_);
lean_dec(v_fst_4933_);
lean_del_object(v___x_4929_);
lean_del_object(v___x_4925_);
lean_del_object(v___x_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_all_4909_);
lean_dec(v_hints_4907_);
lean_del_object(v___x_4903_);
v_a_5031_ = lean_ctor_get(v___x_4952_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5033_ = v___x_4952_;
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v___x_4952_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
}
}
else
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5047_; 
lean_del_object(v___x_4943_);
lean_dec(v_fst_4940_);
lean_del_object(v___x_4936_);
lean_dec(v_fst_4933_);
lean_del_object(v___x_4929_);
lean_del_object(v___x_4925_);
lean_del_object(v___x_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_all_4909_);
lean_dec(v_hints_4907_);
lean_dec_ref(v_value_4906_);
lean_del_object(v___x_4903_);
v_a_5040_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5042_ = v___x_4945_;
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_4945_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5045_; 
if (v_isShared_5043_ == 0)
{
v___x_5045_ = v___x_5042_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_a_5040_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
}
}
else
{
lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5056_; 
lean_del_object(v___x_4936_);
lean_dec(v_fst_4933_);
lean_del_object(v___x_4929_);
lean_del_object(v___x_4925_);
lean_del_object(v___x_4920_);
lean_del_object(v___x_4916_);
lean_dec_ref(v_type_4912_);
lean_dec(v_all_4909_);
lean_dec(v_hints_4907_);
lean_dec_ref(v_value_4906_);
lean_del_object(v___x_4903_);
v_a_5049_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5051_ = v___x_4938_;
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_dec(v___x_4938_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v___x_5054_; 
if (v_isShared_5052_ == 0)
{
v___x_5054_ = v___x_5051_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_a_5049_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
}
}
else
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5065_; 
lean_del_object(v___x_4929_);
lean_del_object(v___x_4925_);
lean_del_object(v___x_4920_);
lean_del_object(v___x_4916_);
lean_dec_ref(v_type_4912_);
lean_dec(v_levelParams_4911_);
lean_dec(v_all_4909_);
lean_dec(v_hints_4907_);
lean_dec_ref(v_value_4906_);
lean_del_object(v___x_4903_);
v_a_5058_ = lean_ctor_get(v___x_4931_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5060_ = v___x_4931_;
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_4931_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4920_);
lean_del_object(v___x_4916_);
lean_dec_ref(v_type_4912_);
lean_dec(v_levelParams_4911_);
lean_dec(v_name_4910_);
lean_dec(v_all_4909_);
lean_dec(v_hints_4907_);
lean_dec_ref(v_value_4906_);
lean_del_object(v___x_4903_);
return v___x_4922_;
}
}
}
}
else
{
lean_dec_ref(v_type_4912_);
lean_dec(v_levelParams_4911_);
lean_dec(v_name_4910_);
lean_dec(v_all_4909_);
lean_dec(v_hints_4907_);
lean_dec_ref(v_value_4906_);
lean_del_object(v___x_4903_);
return v___x_4913_;
}
}
}
case 2:
{
lean_object* v_val_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5234_; 
v_val_5073_ = lean_ctor_get(v_val_4778_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v_val_4778_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5075_ = v_val_4778_;
v_isShared_5076_ = v_isSharedCheck_5234_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_val_5073_);
lean_dec(v_val_4778_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5234_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v_toConstantVal_5077_; lean_object* v_value_5078_; lean_object* v_all_5079_; lean_object* v_name_5080_; lean_object* v_levelParams_5081_; lean_object* v_type_5082_; lean_object* v___x_5083_; 
v_toConstantVal_5077_ = lean_ctor_get(v_val_5073_, 0);
lean_inc_ref(v_toConstantVal_5077_);
v_value_5078_ = lean_ctor_get(v_val_5073_, 1);
lean_inc_ref(v_value_5078_);
v_all_5079_ = lean_ctor_get(v_val_5073_, 2);
lean_inc(v_all_5079_);
lean_dec_ref(v_val_5073_);
v_name_5080_ = lean_ctor_get(v_toConstantVal_5077_, 0);
lean_inc(v_name_5080_);
v_levelParams_5081_ = lean_ctor_get(v_toConstantVal_5077_, 1);
lean_inc(v_levelParams_5081_);
v_type_5082_ = lean_ctor_get(v_toConstantVal_5077_, 2);
lean_inc_ref_n(v_type_5082_, 2);
lean_dec_ref(v_toConstantVal_5077_);
v___x_5083_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5082_, v_a_4667_, v___x_4795_);
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_object* v_a_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5233_; 
v_a_5084_ = lean_ctor_get(v___x_5083_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5083_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5086_ = v___x_5083_;
v_isShared_5087_ = v_isSharedCheck_5233_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_a_5084_);
lean_dec(v___x_5083_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5233_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v_snd_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5231_; 
v_snd_5088_ = lean_ctor_get(v_a_5084_, 1);
v_isSharedCheck_5231_ = !lean_is_exclusive(v_a_5084_);
if (v_isSharedCheck_5231_ == 0)
{
lean_object* v_unused_5232_; 
v_unused_5232_ = lean_ctor_get(v_a_5084_, 0);
lean_dec(v_unused_5232_);
v___x_5090_ = v_a_5084_;
v_isShared_5091_ = v_isSharedCheck_5231_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_snd_5088_);
lean_dec(v_a_5084_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5231_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5092_; 
lean_inc_ref(v_value_5078_);
v___x_5092_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5078_, v_a_4667_, v_snd_5088_);
if (lean_obj_tag(v___x_5092_) == 0)
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5230_; 
v_a_5093_ = lean_ctor_get(v___x_5092_, 0);
v_isSharedCheck_5230_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_5095_ = v___x_5092_;
v_isShared_5096_ = v_isSharedCheck_5230_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5092_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5230_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v_snd_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5228_; 
v_snd_5097_ = lean_ctor_get(v_a_5093_, 1);
v_isSharedCheck_5228_ = !lean_is_exclusive(v_a_5093_);
if (v_isSharedCheck_5228_ == 0)
{
lean_object* v_unused_5229_; 
v_unused_5229_ = lean_ctor_get(v_a_5093_, 0);
lean_dec(v_unused_5229_);
v___x_5099_ = v_a_5093_;
v_isShared_5100_ = v_isSharedCheck_5228_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_snd_5097_);
lean_dec(v_a_5093_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5228_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5101_; 
v___x_5101_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5080_, v_a_4667_, v_snd_5097_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v_a_5102_; lean_object* v_fst_5103_; lean_object* v_snd_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5219_; 
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_a_5102_);
lean_dec_ref_known(v___x_5101_, 1);
v_fst_5103_ = lean_ctor_get(v_a_5102_, 0);
v_snd_5104_ = lean_ctor_get(v_a_5102_, 1);
v_isSharedCheck_5219_ = !lean_is_exclusive(v_a_5102_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5106_ = v_a_5102_;
v_isShared_5107_ = v_isSharedCheck_5219_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_snd_5104_);
lean_inc(v_fst_5103_);
lean_dec(v_a_5102_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5219_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5108_; 
v___x_5108_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5081_, v_a_4667_, v_snd_5104_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; lean_object* v_fst_5110_; lean_object* v_snd_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5210_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5109_);
lean_dec_ref_known(v___x_5108_, 1);
v_fst_5110_ = lean_ctor_get(v_a_5109_, 0);
v_snd_5111_ = lean_ctor_get(v_a_5109_, 1);
v_isSharedCheck_5210_ = !lean_is_exclusive(v_a_5109_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5113_ = v_a_5109_;
v_isShared_5114_ = v_isSharedCheck_5210_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_snd_5111_);
lean_inc(v_fst_5110_);
lean_dec(v_a_5109_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5210_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5115_; 
v___x_5115_ = l_LeanExport_dumpExpr(v_type_5082_, v_a_4667_, v_snd_5111_);
if (lean_obj_tag(v___x_5115_) == 0)
{
lean_object* v_a_5116_; lean_object* v_fst_5117_; lean_object* v_snd_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5201_; 
v_a_5116_ = lean_ctor_get(v___x_5115_, 0);
lean_inc(v_a_5116_);
lean_dec_ref_known(v___x_5115_, 1);
v_fst_5117_ = lean_ctor_get(v_a_5116_, 0);
v_snd_5118_ = lean_ctor_get(v_a_5116_, 1);
v_isSharedCheck_5201_ = !lean_is_exclusive(v_a_5116_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5120_ = v_a_5116_;
v_isShared_5121_ = v_isSharedCheck_5201_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_snd_5118_);
lean_inc(v_fst_5117_);
lean_dec(v_a_5116_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5201_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5122_; 
v___x_5122_ = l_LeanExport_dumpExpr(v_value_5078_, v_a_4667_, v_snd_5118_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v_fst_5124_; lean_object* v_snd_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5192_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_a_5123_);
lean_dec_ref_known(v___x_5122_, 1);
v_fst_5124_ = lean_ctor_get(v_a_5123_, 0);
v_snd_5125_ = lean_ctor_get(v_a_5123_, 1);
v_isSharedCheck_5192_ = !lean_is_exclusive(v_a_5123_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5127_ = v_a_5123_;
v_isShared_5128_ = v_isSharedCheck_5192_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_snd_5125_);
lean_inc(v_fst_5124_);
lean_dec(v_a_5123_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5192_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5129_; 
v___x_5129_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5079_, v_a_4667_, v_snd_5125_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v_fst_5131_; lean_object* v_snd_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5183_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
v_fst_5131_ = lean_ctor_get(v_a_5130_, 0);
v_snd_5132_ = lean_ctor_get(v_a_5130_, 1);
v_isSharedCheck_5183_ = !lean_is_exclusive(v_a_5130_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5134_ = v_a_5130_;
v_isShared_5135_ = v_isSharedCheck_5183_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_snd_5132_);
lean_inc(v_fst_5131_);
lean_dec(v_a_5130_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5183_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5140_; 
v___x_5136_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__7));
v___x_5137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5138_ = l_Lean_JsonNumber_fromNat(v_fst_5103_);
if (v_isShared_5096_ == 0)
{
lean_ctor_set_tag(v___x_5095_, 2);
lean_ctor_set(v___x_5095_, 0, v___x_5138_);
v___x_5140_ = v___x_5095_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v___x_5138_);
v___x_5140_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
lean_object* v___x_5142_; 
if (v_isShared_5135_ == 0)
{
lean_ctor_set(v___x_5134_, 1, v___x_5140_);
lean_ctor_set(v___x_5134_, 0, v___x_5137_);
v___x_5142_ = v___x_5134_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v___x_5137_);
lean_ctor_set(v_reuseFailAlloc_5181_, 1, v___x_5140_);
v___x_5142_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
lean_object* v___x_5143_; lean_object* v___x_5145_; 
v___x_5143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5128_ == 0)
{
lean_ctor_set(v___x_5127_, 1, v_fst_5110_);
lean_ctor_set(v___x_5127_, 0, v___x_5143_);
v___x_5145_ = v___x_5127_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v___x_5143_);
lean_ctor_set(v_reuseFailAlloc_5180_, 1, v_fst_5110_);
v___x_5145_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5149_; 
v___x_5146_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5147_ = l_Lean_JsonNumber_fromNat(v_fst_5117_);
if (v_isShared_5087_ == 0)
{
lean_ctor_set_tag(v___x_5086_, 2);
lean_ctor_set(v___x_5086_, 0, v___x_5147_);
v___x_5149_ = v___x_5086_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5147_);
v___x_5149_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
lean_object* v___x_5151_; 
if (v_isShared_5121_ == 0)
{
lean_ctor_set(v___x_5120_, 1, v___x_5149_);
lean_ctor_set(v___x_5120_, 0, v___x_5146_);
v___x_5151_ = v___x_5120_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v___x_5146_);
lean_ctor_set(v_reuseFailAlloc_5178_, 1, v___x_5149_);
v___x_5151_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5155_; 
v___x_5152_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5153_ = l_Lean_JsonNumber_fromNat(v_fst_5124_);
if (v_isShared_5076_ == 0)
{
lean_ctor_set(v___x_5075_, 0, v___x_5153_);
v___x_5155_ = v___x_5075_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v___x_5153_);
v___x_5155_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
lean_object* v___x_5157_; 
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 1, v___x_5155_);
lean_ctor_set(v___x_5113_, 0, v___x_5152_);
v___x_5157_ = v___x_5113_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5152_);
lean_ctor_set(v_reuseFailAlloc_5176_, 1, v___x_5155_);
v___x_5157_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
lean_object* v___x_5158_; lean_object* v___x_5160_; 
v___x_5158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_5107_ == 0)
{
lean_ctor_set(v___x_5106_, 1, v_fst_5131_);
lean_ctor_set(v___x_5106_, 0, v___x_5158_);
v___x_5160_ = v___x_5106_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5158_);
lean_ctor_set(v_reuseFailAlloc_5175_, 1, v_fst_5131_);
v___x_5160_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
lean_object* v___x_5161_; lean_object* v___x_5163_; 
v___x_5161_ = lean_box(0);
if (v_isShared_5091_ == 0)
{
lean_ctor_set_tag(v___x_5090_, 1);
lean_ctor_set(v___x_5090_, 1, v___x_5161_);
lean_ctor_set(v___x_5090_, 0, v___x_5160_);
v___x_5163_ = v___x_5090_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5160_);
lean_ctor_set(v_reuseFailAlloc_5174_, 1, v___x_5161_);
v___x_5163_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5170_; 
v___x_5164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5157_);
lean_ctor_set(v___x_5164_, 1, v___x_5163_);
v___x_5165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5165_, 0, v___x_5151_);
lean_ctor_set(v___x_5165_, 1, v___x_5164_);
v___x_5166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5166_, 0, v___x_5145_);
lean_ctor_set(v___x_5166_, 1, v___x_5165_);
v___x_5167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5167_, 0, v___x_5142_);
lean_ctor_set(v___x_5167_, 1, v___x_5166_);
v___x_5168_ = l_Lean_Json_mkObj(v___x_5167_);
lean_dec_ref_known(v___x_5167_, 2);
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 1, v___x_5168_);
lean_ctor_set(v___x_5099_, 0, v___x_5136_);
v___x_5170_ = v___x_5099_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5136_);
lean_ctor_set(v_reuseFailAlloc_5173_, 1, v___x_5168_);
v___x_5170_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___x_5171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5170_);
lean_ctor_set(v___x_5171_, 1, v___x_5161_);
v___x_5172_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5171_, v_snd_5132_);
lean_dec_ref_known(v___x_5171_, 2);
return v___x_5172_;
}
}
}
}
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
lean_object* v_a_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5191_; 
lean_del_object(v___x_5127_);
lean_dec(v_fst_5124_);
lean_del_object(v___x_5120_);
lean_dec(v_fst_5117_);
lean_del_object(v___x_5113_);
lean_dec(v_fst_5110_);
lean_del_object(v___x_5106_);
lean_dec(v_fst_5103_);
lean_del_object(v___x_5099_);
lean_del_object(v___x_5095_);
lean_del_object(v___x_5090_);
lean_del_object(v___x_5086_);
lean_del_object(v___x_5075_);
v_a_5184_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5186_ = v___x_5129_;
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_a_5184_);
lean_dec(v___x_5129_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5189_; 
if (v_isShared_5187_ == 0)
{
v___x_5189_ = v___x_5186_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
lean_del_object(v___x_5120_);
lean_dec(v_fst_5117_);
lean_del_object(v___x_5113_);
lean_dec(v_fst_5110_);
lean_del_object(v___x_5106_);
lean_dec(v_fst_5103_);
lean_del_object(v___x_5099_);
lean_del_object(v___x_5095_);
lean_del_object(v___x_5090_);
lean_del_object(v___x_5086_);
lean_dec(v_all_5079_);
lean_del_object(v___x_5075_);
v_a_5193_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5122_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5122_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
}
else
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
lean_del_object(v___x_5113_);
lean_dec(v_fst_5110_);
lean_del_object(v___x_5106_);
lean_dec(v_fst_5103_);
lean_del_object(v___x_5099_);
lean_del_object(v___x_5095_);
lean_del_object(v___x_5090_);
lean_del_object(v___x_5086_);
lean_dec(v_all_5079_);
lean_dec_ref(v_value_5078_);
lean_del_object(v___x_5075_);
v_a_5202_ = lean_ctor_get(v___x_5115_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5115_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5115_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
}
}
else
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
lean_del_object(v___x_5106_);
lean_dec(v_fst_5103_);
lean_del_object(v___x_5099_);
lean_del_object(v___x_5095_);
lean_del_object(v___x_5090_);
lean_del_object(v___x_5086_);
lean_dec_ref(v_type_5082_);
lean_dec(v_all_5079_);
lean_dec_ref(v_value_5078_);
lean_del_object(v___x_5075_);
v_a_5211_ = lean_ctor_get(v___x_5108_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5108_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5108_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5108_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
}
}
else
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
lean_del_object(v___x_5099_);
lean_del_object(v___x_5095_);
lean_del_object(v___x_5090_);
lean_del_object(v___x_5086_);
lean_dec_ref(v_type_5082_);
lean_dec(v_levelParams_5081_);
lean_dec(v_all_5079_);
lean_dec_ref(v_value_5078_);
lean_del_object(v___x_5075_);
v_a_5220_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v___x_5101_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5101_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_a_5220_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5090_);
lean_del_object(v___x_5086_);
lean_dec_ref(v_type_5082_);
lean_dec(v_levelParams_5081_);
lean_dec(v_name_5080_);
lean_dec(v_all_5079_);
lean_dec_ref(v_value_5078_);
lean_del_object(v___x_5075_);
return v___x_5092_;
}
}
}
}
else
{
lean_dec_ref(v_type_5082_);
lean_dec(v_levelParams_5081_);
lean_dec(v_name_5080_);
lean_dec(v_all_5079_);
lean_dec_ref(v_value_5078_);
lean_del_object(v___x_5075_);
return v___x_5083_;
}
}
}
case 3:
{
lean_object* v_val_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5401_; 
v_val_5235_ = lean_ctor_get(v_val_4778_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v_val_4778_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5237_ = v_val_4778_;
v_isShared_5238_ = v_isSharedCheck_5401_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_val_5235_);
lean_dec(v_val_4778_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5401_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v_toConstantVal_5239_; lean_object* v_value_5240_; uint8_t v_isUnsafe_5241_; lean_object* v_all_5242_; lean_object* v_name_5243_; lean_object* v_levelParams_5244_; lean_object* v_type_5245_; lean_object* v___x_5246_; 
v_toConstantVal_5239_ = lean_ctor_get(v_val_5235_, 0);
lean_inc_ref(v_toConstantVal_5239_);
v_value_5240_ = lean_ctor_get(v_val_5235_, 1);
lean_inc_ref(v_value_5240_);
v_isUnsafe_5241_ = lean_ctor_get_uint8(v_val_5235_, sizeof(void*)*3);
v_all_5242_ = lean_ctor_get(v_val_5235_, 2);
lean_inc(v_all_5242_);
lean_dec_ref(v_val_5235_);
v_name_5243_ = lean_ctor_get(v_toConstantVal_5239_, 0);
lean_inc(v_name_5243_);
v_levelParams_5244_ = lean_ctor_get(v_toConstantVal_5239_, 1);
lean_inc(v_levelParams_5244_);
v_type_5245_ = lean_ctor_get(v_toConstantVal_5239_, 2);
lean_inc_ref_n(v_type_5245_, 2);
lean_dec_ref(v_toConstantVal_5239_);
v___x_5246_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5245_, v_a_4667_, v___x_4795_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5400_; 
v_a_5247_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5249_ = v___x_5246_;
v_isShared_5250_ = v_isSharedCheck_5400_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5246_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5400_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v_snd_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5398_; 
v_snd_5251_ = lean_ctor_get(v_a_5247_, 1);
v_isSharedCheck_5398_ = !lean_is_exclusive(v_a_5247_);
if (v_isSharedCheck_5398_ == 0)
{
lean_object* v_unused_5399_; 
v_unused_5399_ = lean_ctor_get(v_a_5247_, 0);
lean_dec(v_unused_5399_);
v___x_5253_ = v_a_5247_;
v_isShared_5254_ = v_isSharedCheck_5398_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_snd_5251_);
lean_dec(v_a_5247_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5398_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v___x_5255_; 
lean_inc_ref(v_value_5240_);
v___x_5255_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5240_, v_a_4667_, v_snd_5251_);
if (lean_obj_tag(v___x_5255_) == 0)
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5397_; 
v_a_5256_ = lean_ctor_get(v___x_5255_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5258_ = v___x_5255_;
v_isShared_5259_ = v_isSharedCheck_5397_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5255_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5397_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v_snd_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5395_; 
v_snd_5260_ = lean_ctor_get(v_a_5256_, 1);
v_isSharedCheck_5395_ = !lean_is_exclusive(v_a_5256_);
if (v_isSharedCheck_5395_ == 0)
{
lean_object* v_unused_5396_; 
v_unused_5396_ = lean_ctor_get(v_a_5256_, 0);
lean_dec(v_unused_5396_);
v___x_5262_ = v_a_5256_;
v_isShared_5263_ = v_isSharedCheck_5395_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_snd_5260_);
lean_dec(v_a_5256_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5395_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5264_; 
v___x_5264_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5243_, v_a_4667_, v_snd_5260_);
if (lean_obj_tag(v___x_5264_) == 0)
{
lean_object* v_a_5265_; lean_object* v_fst_5266_; lean_object* v_snd_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5386_; 
v_a_5265_ = lean_ctor_get(v___x_5264_, 0);
lean_inc(v_a_5265_);
lean_dec_ref_known(v___x_5264_, 1);
v_fst_5266_ = lean_ctor_get(v_a_5265_, 0);
v_snd_5267_ = lean_ctor_get(v_a_5265_, 1);
v_isSharedCheck_5386_ = !lean_is_exclusive(v_a_5265_);
if (v_isSharedCheck_5386_ == 0)
{
v___x_5269_ = v_a_5265_;
v_isShared_5270_ = v_isSharedCheck_5386_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_snd_5267_);
lean_inc(v_fst_5266_);
lean_dec(v_a_5265_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5386_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5271_; 
v___x_5271_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5244_, v_a_4667_, v_snd_5267_);
if (lean_obj_tag(v___x_5271_) == 0)
{
lean_object* v_a_5272_; lean_object* v_fst_5273_; lean_object* v_snd_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5377_; 
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
lean_inc(v_a_5272_);
lean_dec_ref_known(v___x_5271_, 1);
v_fst_5273_ = lean_ctor_get(v_a_5272_, 0);
v_snd_5274_ = lean_ctor_get(v_a_5272_, 1);
v_isSharedCheck_5377_ = !lean_is_exclusive(v_a_5272_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5276_ = v_a_5272_;
v_isShared_5277_ = v_isSharedCheck_5377_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_snd_5274_);
lean_inc(v_fst_5273_);
lean_dec(v_a_5272_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5377_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5278_; 
v___x_5278_ = l_LeanExport_dumpExpr(v_type_5245_, v_a_4667_, v_snd_5274_);
if (lean_obj_tag(v___x_5278_) == 0)
{
lean_object* v_a_5279_; lean_object* v_fst_5280_; lean_object* v_snd_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5368_; 
v_a_5279_ = lean_ctor_get(v___x_5278_, 0);
lean_inc(v_a_5279_);
lean_dec_ref_known(v___x_5278_, 1);
v_fst_5280_ = lean_ctor_get(v_a_5279_, 0);
v_snd_5281_ = lean_ctor_get(v_a_5279_, 1);
v_isSharedCheck_5368_ = !lean_is_exclusive(v_a_5279_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5283_ = v_a_5279_;
v_isShared_5284_ = v_isSharedCheck_5368_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_snd_5281_);
lean_inc(v_fst_5280_);
lean_dec(v_a_5279_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5368_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5285_; 
v___x_5285_ = l_LeanExport_dumpExpr(v_value_5240_, v_a_4667_, v_snd_5281_);
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v_a_5286_; lean_object* v_fst_5287_; lean_object* v_snd_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5359_; 
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc(v_a_5286_);
lean_dec_ref_known(v___x_5285_, 1);
v_fst_5287_ = lean_ctor_get(v_a_5286_, 0);
v_snd_5288_ = lean_ctor_get(v_a_5286_, 1);
v_isSharedCheck_5359_ = !lean_is_exclusive(v_a_5286_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5290_ = v_a_5286_;
v_isShared_5291_ = v_isSharedCheck_5359_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_snd_5288_);
lean_inc(v_fst_5287_);
lean_dec(v_a_5286_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5359_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5292_; 
v___x_5292_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5242_, v_a_4667_, v_snd_5288_);
if (lean_obj_tag(v___x_5292_) == 0)
{
lean_object* v_a_5293_; lean_object* v_fst_5294_; lean_object* v_snd_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5350_; 
v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
lean_inc(v_a_5293_);
lean_dec_ref_known(v___x_5292_, 1);
v_fst_5294_ = lean_ctor_get(v_a_5293_, 0);
v_snd_5295_ = lean_ctor_get(v_a_5293_, 1);
v_isSharedCheck_5350_ = !lean_is_exclusive(v_a_5293_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5297_ = v_a_5293_;
v_isShared_5298_ = v_isSharedCheck_5350_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_snd_5295_);
lean_inc(v_fst_5294_);
lean_dec(v_a_5293_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5350_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5303_; 
v___x_5299_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0));
v___x_5300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5301_ = l_Lean_JsonNumber_fromNat(v_fst_5266_);
if (v_isShared_5259_ == 0)
{
lean_ctor_set_tag(v___x_5258_, 2);
lean_ctor_set(v___x_5258_, 0, v___x_5301_);
v___x_5303_ = v___x_5258_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v___x_5301_);
v___x_5303_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
lean_object* v___x_5305_; 
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 1, v___x_5303_);
lean_ctor_set(v___x_5297_, 0, v___x_5300_);
v___x_5305_ = v___x_5297_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v___x_5300_);
lean_ctor_set(v_reuseFailAlloc_5348_, 1, v___x_5303_);
v___x_5305_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
lean_object* v___x_5306_; lean_object* v___x_5308_; 
v___x_5306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 1, v_fst_5273_);
lean_ctor_set(v___x_5290_, 0, v___x_5306_);
v___x_5308_ = v___x_5290_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v___x_5306_);
lean_ctor_set(v_reuseFailAlloc_5347_, 1, v_fst_5273_);
v___x_5308_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5312_; 
v___x_5309_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5310_ = l_Lean_JsonNumber_fromNat(v_fst_5280_);
if (v_isShared_5250_ == 0)
{
lean_ctor_set_tag(v___x_5249_, 2);
lean_ctor_set(v___x_5249_, 0, v___x_5310_);
v___x_5312_ = v___x_5249_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5310_);
v___x_5312_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
lean_object* v___x_5314_; 
if (v_isShared_5284_ == 0)
{
lean_ctor_set(v___x_5283_, 1, v___x_5312_);
lean_ctor_set(v___x_5283_, 0, v___x_5309_);
v___x_5314_ = v___x_5283_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v___x_5309_);
lean_ctor_set(v_reuseFailAlloc_5345_, 1, v___x_5312_);
v___x_5314_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5318_; 
v___x_5315_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5316_ = l_Lean_JsonNumber_fromNat(v_fst_5287_);
if (v_isShared_5238_ == 0)
{
lean_ctor_set_tag(v___x_5237_, 2);
lean_ctor_set(v___x_5237_, 0, v___x_5316_);
v___x_5318_ = v___x_5237_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v___x_5316_);
v___x_5318_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
lean_object* v___x_5320_; 
if (v_isShared_5277_ == 0)
{
lean_ctor_set(v___x_5276_, 1, v___x_5318_);
lean_ctor_set(v___x_5276_, 0, v___x_5315_);
v___x_5320_ = v___x_5276_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v___x_5315_);
lean_ctor_set(v_reuseFailAlloc_5343_, 1, v___x_5318_);
v___x_5320_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
lean_object* v___x_5321_; lean_object* v___x_5323_; 
v___x_5321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_5270_ == 0)
{
lean_ctor_set(v___x_5269_, 1, v_fst_5294_);
lean_ctor_set(v___x_5269_, 0, v___x_5321_);
v___x_5323_ = v___x_5269_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5321_);
lean_ctor_set(v_reuseFailAlloc_5342_, 1, v_fst_5294_);
v___x_5323_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5327_; 
v___x_5324_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_5325_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5325_, 0, v_isUnsafe_5241_);
if (v_isShared_5263_ == 0)
{
lean_ctor_set(v___x_5262_, 1, v___x_5325_);
lean_ctor_set(v___x_5262_, 0, v___x_5324_);
v___x_5327_ = v___x_5262_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v___x_5324_);
lean_ctor_set(v_reuseFailAlloc_5341_, 1, v___x_5325_);
v___x_5327_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5337_; 
v___x_5328_ = lean_box(0);
v___x_5329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5327_);
lean_ctor_set(v___x_5329_, 1, v___x_5328_);
v___x_5330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5330_, 0, v___x_5323_);
lean_ctor_set(v___x_5330_, 1, v___x_5329_);
v___x_5331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5320_);
lean_ctor_set(v___x_5331_, 1, v___x_5330_);
v___x_5332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5332_, 0, v___x_5314_);
lean_ctor_set(v___x_5332_, 1, v___x_5331_);
v___x_5333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5333_, 0, v___x_5308_);
lean_ctor_set(v___x_5333_, 1, v___x_5332_);
v___x_5334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5334_, 0, v___x_5305_);
lean_ctor_set(v___x_5334_, 1, v___x_5333_);
v___x_5335_ = l_Lean_Json_mkObj(v___x_5334_);
lean_dec_ref_known(v___x_5334_, 2);
if (v_isShared_5254_ == 0)
{
lean_ctor_set(v___x_5253_, 1, v___x_5335_);
lean_ctor_set(v___x_5253_, 0, v___x_5299_);
v___x_5337_ = v___x_5253_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v___x_5299_);
lean_ctor_set(v_reuseFailAlloc_5340_, 1, v___x_5335_);
v___x_5337_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
lean_object* v___x_5338_; lean_object* v___x_5339_; 
v___x_5338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5337_);
lean_ctor_set(v___x_5338_, 1, v___x_5328_);
v___x_5339_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5338_, v_snd_5295_);
lean_dec_ref_known(v___x_5338_, 2);
return v___x_5339_;
}
}
}
}
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
lean_object* v_a_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5358_; 
lean_del_object(v___x_5290_);
lean_dec(v_fst_5287_);
lean_del_object(v___x_5283_);
lean_dec(v_fst_5280_);
lean_del_object(v___x_5276_);
lean_dec(v_fst_5273_);
lean_del_object(v___x_5269_);
lean_dec(v_fst_5266_);
lean_del_object(v___x_5262_);
lean_del_object(v___x_5258_);
lean_del_object(v___x_5253_);
lean_del_object(v___x_5249_);
lean_del_object(v___x_5237_);
v_a_5351_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5353_ = v___x_5292_;
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_a_5351_);
lean_dec(v___x_5292_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v___x_5356_; 
if (v_isShared_5354_ == 0)
{
v___x_5356_ = v___x_5353_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5351_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_del_object(v___x_5283_);
lean_dec(v_fst_5280_);
lean_del_object(v___x_5276_);
lean_dec(v_fst_5273_);
lean_del_object(v___x_5269_);
lean_dec(v_fst_5266_);
lean_del_object(v___x_5262_);
lean_del_object(v___x_5258_);
lean_del_object(v___x_5253_);
lean_del_object(v___x_5249_);
lean_dec(v_all_5242_);
lean_del_object(v___x_5237_);
v_a_5360_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5285_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5285_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
else
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5376_; 
lean_del_object(v___x_5276_);
lean_dec(v_fst_5273_);
lean_del_object(v___x_5269_);
lean_dec(v_fst_5266_);
lean_del_object(v___x_5262_);
lean_del_object(v___x_5258_);
lean_del_object(v___x_5253_);
lean_del_object(v___x_5249_);
lean_dec(v_all_5242_);
lean_dec_ref(v_value_5240_);
lean_del_object(v___x_5237_);
v_a_5369_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5371_ = v___x_5278_;
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v___x_5278_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5374_; 
if (v_isShared_5372_ == 0)
{
v___x_5374_ = v___x_5371_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
}
}
else
{
lean_object* v_a_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5385_; 
lean_del_object(v___x_5269_);
lean_dec(v_fst_5266_);
lean_del_object(v___x_5262_);
lean_del_object(v___x_5258_);
lean_del_object(v___x_5253_);
lean_del_object(v___x_5249_);
lean_dec_ref(v_type_5245_);
lean_dec(v_all_5242_);
lean_dec_ref(v_value_5240_);
lean_del_object(v___x_5237_);
v_a_5378_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5380_ = v___x_5271_;
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_a_5378_);
lean_dec(v___x_5271_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v___x_5383_; 
if (v_isShared_5381_ == 0)
{
v___x_5383_ = v___x_5380_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
}
}
}
else
{
lean_object* v_a_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5394_; 
lean_del_object(v___x_5262_);
lean_del_object(v___x_5258_);
lean_del_object(v___x_5253_);
lean_del_object(v___x_5249_);
lean_dec_ref(v_type_5245_);
lean_dec(v_levelParams_5244_);
lean_dec(v_all_5242_);
lean_dec_ref(v_value_5240_);
lean_del_object(v___x_5237_);
v_a_5387_ = lean_ctor_get(v___x_5264_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5264_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5389_ = v___x_5264_;
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_a_5387_);
lean_dec(v___x_5264_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v___x_5392_; 
if (v_isShared_5390_ == 0)
{
v___x_5392_ = v___x_5389_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_a_5387_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5253_);
lean_del_object(v___x_5249_);
lean_dec_ref(v_type_5245_);
lean_dec(v_levelParams_5244_);
lean_dec(v_name_5243_);
lean_dec(v_all_5242_);
lean_dec_ref(v_value_5240_);
lean_del_object(v___x_5237_);
return v___x_5255_;
}
}
}
}
else
{
lean_dec_ref(v_type_5245_);
lean_dec(v_levelParams_5244_);
lean_dec(v_name_5243_);
lean_dec(v_all_5242_);
lean_dec_ref(v_value_5240_);
lean_del_object(v___x_5237_);
return v___x_5246_;
}
}
}
case 4:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; 
lean_dec_ref_known(v_val_4778_, 1);
v___x_5402_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__9));
v___x_5403_ = l_LeanExport_dumpConstant(v___x_5402_, v_a_4667_, v___x_4795_);
if (lean_obj_tag(v___x_5403_) == 0)
{
lean_object* v_a_5404_; lean_object* v_snd_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; 
v_a_5404_ = lean_ctor_get(v___x_5403_, 0);
lean_inc(v_a_5404_);
lean_dec_ref_known(v___x_5403_, 1);
v_snd_5405_ = lean_ctor_get(v_a_5404_, 1);
lean_inc(v_snd_5405_);
lean_dec(v_a_5404_);
v___x_5406_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__19));
v___x_5407_ = lean_box(0);
v___x_5408_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
v___x_5409_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_4789_, v___x_5406_, v___x_5408_, v_a_4667_, v_snd_5405_);
if (lean_obj_tag(v___x_5409_) == 0)
{
lean_object* v_a_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5436_; 
v_a_5410_ = lean_ctor_get(v___x_5409_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5409_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5412_ = v___x_5409_;
v_isShared_5413_ = v_isSharedCheck_5436_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_a_5410_);
lean_dec(v___x_5409_);
v___x_5412_ = lean_box(0);
v_isShared_5413_ = v_isSharedCheck_5436_;
goto v_resetjp_5411_;
}
v_resetjp_5411_:
{
lean_object* v_fst_5414_; lean_object* v_fst_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5434_; 
v_fst_5414_ = lean_ctor_get(v_a_5410_, 0);
lean_inc(v_fst_5414_);
v_fst_5415_ = lean_ctor_get(v_fst_5414_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v_fst_5414_);
if (v_isSharedCheck_5434_ == 0)
{
lean_object* v_unused_5435_; 
v_unused_5435_ = lean_ctor_get(v_fst_5414_, 1);
lean_dec(v_unused_5435_);
v___x_5417_ = v_fst_5414_;
v_isShared_5418_ = v_isSharedCheck_5434_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_fst_5415_);
lean_dec(v_fst_5414_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5434_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
if (lean_obj_tag(v_fst_5415_) == 0)
{
lean_object* v_snd_5419_; lean_object* v___x_5421_; 
v_snd_5419_ = lean_ctor_get(v_a_5410_, 1);
lean_inc(v_snd_5419_);
lean_dec(v_a_5410_);
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 1, v_snd_5419_);
lean_ctor_set(v___x_5417_, 0, v___x_5407_);
v___x_5421_ = v___x_5417_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v___x_5407_);
lean_ctor_set(v_reuseFailAlloc_5425_, 1, v_snd_5419_);
v___x_5421_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
lean_object* v___x_5423_; 
if (v_isShared_5413_ == 0)
{
lean_ctor_set(v___x_5412_, 0, v___x_5421_);
v___x_5423_ = v___x_5412_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v___x_5421_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
return v___x_5423_;
}
}
}
else
{
lean_object* v_snd_5426_; lean_object* v_val_5427_; lean_object* v___x_5429_; 
v_snd_5426_ = lean_ctor_get(v_a_5410_, 1);
lean_inc(v_snd_5426_);
lean_dec(v_a_5410_);
v_val_5427_ = lean_ctor_get(v_fst_5415_, 0);
lean_inc(v_val_5427_);
lean_dec_ref_known(v_fst_5415_, 1);
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 1, v_snd_5426_);
lean_ctor_set(v___x_5417_, 0, v_val_5427_);
v___x_5429_ = v___x_5417_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_val_5427_);
lean_ctor_set(v_reuseFailAlloc_5433_, 1, v_snd_5426_);
v___x_5429_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
lean_object* v___x_5431_; 
if (v_isShared_5413_ == 0)
{
lean_ctor_set(v___x_5412_, 0, v___x_5429_);
v___x_5431_ = v___x_5412_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v___x_5429_);
v___x_5431_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
return v___x_5431_;
}
}
}
}
}
}
else
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5444_; 
v_a_5437_ = lean_ctor_get(v___x_5409_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5409_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5439_ = v___x_5409_;
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5409_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
}
else
{
return v___x_5403_;
}
}
case 5:
{
lean_object* v_val_5445_; lean_object* v_all_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; 
v_val_5445_ = lean_ctor_get(v_val_4778_, 0);
lean_inc_ref(v_val_5445_);
lean_dec_ref_known(v_val_4778_, 1);
v_all_5446_ = lean_ctor_get(v_val_5445_, 3);
lean_inc(v_all_5446_);
v___x_5447_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_5448_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__22, &l_LeanExport_dumpConstant___closed__22_once, _init_l_LeanExport_dumpConstant___closed__22);
v___x_5449_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_4789_, v_val_5445_, v_all_5446_, v___x_5448_, v_a_4667_, v___x_4795_);
lean_dec(v_all_5446_);
lean_dec_ref(v_val_5445_);
if (lean_obj_tag(v___x_5449_) == 0)
{
lean_object* v_a_5450_; lean_object* v_fst_5451_; lean_object* v_snd_5452_; lean_object* v_snd_5453_; lean_object* v_fst_5454_; lean_object* v_fst_5455_; lean_object* v_snd_5456_; lean_object* v___x_5457_; size_t v_sz_5458_; size_t v___x_5459_; lean_object* v___x_5460_; 
v_a_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_a_5450_);
lean_dec_ref_known(v___x_5449_, 1);
v_fst_5451_ = lean_ctor_get(v_a_5450_, 0);
lean_inc(v_fst_5451_);
v_snd_5452_ = lean_ctor_get(v_fst_5451_, 1);
lean_inc(v_snd_5452_);
v_snd_5453_ = lean_ctor_get(v_a_5450_, 1);
lean_inc(v_snd_5453_);
lean_dec(v_a_5450_);
v_fst_5454_ = lean_ctor_get(v_fst_5451_, 0);
lean_inc(v_fst_5454_);
lean_dec(v_fst_5451_);
v_fst_5455_ = lean_ctor_get(v_snd_5452_, 0);
lean_inc(v_fst_5455_);
v_snd_5456_ = lean_ctor_get(v_snd_5452_, 1);
lean_inc(v_snd_5456_);
lean_dec(v_snd_5452_);
v___x_5457_ = lean_box(0);
v_sz_5458_ = lean_array_size(v_fst_5455_);
v___x_5459_ = ((size_t)0ULL);
v___x_5460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(v_fst_5455_, v_sz_5458_, v___x_5459_, v___x_5457_, v_a_4667_, v_snd_5453_);
if (lean_obj_tag(v___x_5460_) == 0)
{
lean_object* v_a_5461_; lean_object* v_snd_5462_; lean_object* v___x_5463_; 
v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
lean_inc(v_a_5461_);
lean_dec_ref_known(v___x_5460_, 1);
v_snd_5462_ = lean_ctor_get(v_a_5461_, 1);
lean_inc(v_snd_5462_);
lean_dec(v_a_5461_);
v___x_5463_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_4789_, v___x_5447_, v_snd_5456_, v_a_4667_, v_snd_5462_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; lean_object* v_fst_5465_; lean_object* v_snd_5466_; lean_object* v_a_5467_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc(v_a_5464_);
lean_dec_ref_known(v___x_5463_, 1);
v_fst_5465_ = lean_ctor_get(v_a_5464_, 0);
lean_inc(v_fst_5465_);
v_snd_5466_ = lean_ctor_get(v_a_5464_, 1);
lean_inc(v_snd_5466_);
lean_dec(v_a_5464_);
v_a_5467_ = lean_ctor_get(v_fst_5465_, 0);
lean_inc(v_a_5467_);
lean_dec(v_fst_5465_);
v___y_4675_ = v___x_5457_;
v___y_4676_ = v_fst_5455_;
v___y_4677_ = v_fst_5454_;
v_fst_4678_ = v_a_5467_;
v_snd_4679_ = v_snd_5466_;
goto v___jp_4674_;
}
else
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5475_; 
lean_dec(v_fst_5455_);
lean_dec(v_fst_5454_);
v_a_5468_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5470_ = v___x_5463_;
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v___x_5463_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5473_; 
if (v_isShared_5471_ == 0)
{
v___x_5473_ = v___x_5470_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_a_5468_);
v___x_5473_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
return v___x_5473_;
}
}
}
}
else
{
lean_dec(v_snd_5456_);
lean_dec(v_fst_5455_);
lean_dec(v_fst_5454_);
return v___x_5460_;
}
}
else
{
lean_object* v_a_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5483_; 
v_a_5476_ = lean_ctor_get(v___x_5449_, 0);
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5449_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5478_ = v___x_5449_;
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_a_5476_);
lean_dec(v___x_5449_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v___x_5481_; 
if (v_isShared_5479_ == 0)
{
v___x_5481_ = v___x_5478_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_a_5476_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
}
case 6:
{
lean_object* v_val_5484_; lean_object* v_induct_5485_; 
v_val_5484_ = lean_ctor_get(v_val_4778_, 0);
lean_inc_ref(v_val_5484_);
lean_dec_ref_known(v_val_4778_, 1);
v_induct_5485_ = lean_ctor_get(v_val_5484_, 1);
lean_inc(v_induct_5485_);
lean_dec_ref(v_val_5484_);
v_c_4666_ = v_induct_5485_;
v_a_4668_ = v___x_4795_;
goto _start;
}
default: 
{
lean_object* v_val_5487_; lean_object* v_all_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; 
v_val_5487_ = lean_ctor_get(v_val_4778_, 0);
lean_inc_ref(v_val_5487_);
lean_dec_ref_known(v_val_4778_, 1);
v_all_5488_ = lean_ctor_get(v_val_5487_, 1);
lean_inc(v_all_5488_);
lean_dec_ref(v_val_5487_);
v___x_5489_ = lean_box(0);
v___x_5490_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_all_5488_, v___x_5489_, v_a_4667_, v___x_4795_);
lean_dec(v_all_5488_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5507_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
v_isSharedCheck_5507_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5507_ == 0)
{
v___x_5493_ = v___x_5490_;
v_isShared_5494_ = v_isSharedCheck_5507_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_a_5491_);
lean_dec(v___x_5490_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5507_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v_snd_5495_; lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5505_; 
v_snd_5495_ = lean_ctor_get(v_a_5491_, 1);
v_isSharedCheck_5505_ = !lean_is_exclusive(v_a_5491_);
if (v_isSharedCheck_5505_ == 0)
{
lean_object* v_unused_5506_; 
v_unused_5506_ = lean_ctor_get(v_a_5491_, 0);
lean_dec(v_unused_5506_);
v___x_5497_ = v_a_5491_;
v_isShared_5498_ = v_isSharedCheck_5505_;
goto v_resetjp_5496_;
}
else
{
lean_inc(v_snd_5495_);
lean_dec(v_a_5491_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5505_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
lean_object* v___x_5500_; 
if (v_isShared_5498_ == 0)
{
lean_ctor_set(v___x_5497_, 0, v___x_5489_);
v___x_5500_ = v___x_5497_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v___x_5489_);
lean_ctor_set(v_reuseFailAlloc_5504_, 1, v_snd_5495_);
v___x_5500_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
lean_object* v___x_5502_; 
if (v_isShared_5494_ == 0)
{
lean_ctor_set(v___x_5493_, 0, v___x_5500_);
v___x_5502_ = v___x_5493_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5500_);
v___x_5502_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
return v___x_5502_;
}
}
}
}
}
else
{
return v___x_5490_;
}
}
}
}
}
}
else
{
lean_dec(v_val_4778_);
lean_dec(v_c_4666_);
goto v___jp_4670_;
}
}
}
else
{
uint8_t v_ignoreMissing_5518_; 
lean_dec(v___x_4777_);
v_ignoreMissing_5518_ = lean_ctor_get_uint8(v_a_4668_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_5518_ == 0)
{
lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; uint8_t v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; 
v___x_5519_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_5520_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_5521_ = lean_unsigned_to_nat(254u);
v___x_5522_ = lean_unsigned_to_nat(48u);
v___x_5523_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_5524_ = 1;
v___x_5525_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_4666_, v___x_5524_);
v___x_5526_ = lean_string_append(v___x_5523_, v___x_5525_);
lean_dec_ref(v___x_5525_);
v___x_5527_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_5528_ = lean_string_append(v___x_5526_, v___x_5527_);
v___x_5529_ = l_mkPanicMessageWithDecl(v___x_5519_, v___x_5520_, v___x_5521_, v___x_5522_, v___x_5528_);
lean_dec_ref(v___x_5528_);
v___x_5530_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_5529_, v_a_4667_, v_a_4668_);
return v___x_5530_;
}
else
{
lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
lean_dec(v_c_4666_);
v___x_5531_ = lean_box(0);
v___x_5532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5531_);
lean_ctor_set(v___x_5532_, 1, v_a_4668_);
v___x_5533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5533_, 0, v___x_5532_);
return v___x_5533_;
}
}
v___jp_4670_:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4671_ = lean_box(0);
v___x_4672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4671_);
lean_ctor_set(v___x_4672_, 1, v_a_4668_);
v___x_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4672_);
return v___x_4673_;
}
v___jp_4674_:
{
size_t v_sz_4680_; size_t v___x_4681_; lean_object* v___x_4682_; 
v_sz_4680_ = lean_array_size(v_fst_4678_);
v___x_4681_ = ((size_t)0ULL);
v___x_4682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_fst_4678_, v_sz_4680_, v___x_4681_, v___y_4675_, v_a_4667_, v_snd_4679_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v_snd_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4774_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_a_4683_);
lean_dec_ref_known(v___x_4682_, 1);
v_snd_4684_ = lean_ctor_get(v_a_4683_, 1);
v_isSharedCheck_4774_ = !lean_is_exclusive(v_a_4683_);
if (v_isSharedCheck_4774_ == 0)
{
lean_object* v_unused_4775_; 
v_unused_4775_ = lean_ctor_get(v_a_4683_, 0);
lean_dec(v_unused_4775_);
v___x_4686_ = v_a_4683_;
v_isShared_4687_ = v_isSharedCheck_4774_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_snd_4684_);
lean_dec(v_a_4683_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4774_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4688_; 
v___x_4688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(v_fst_4678_, v_sz_4680_, v___x_4681_, v___y_4675_, v_a_4667_, v_snd_4684_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v_snd_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4772_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_a_4689_);
lean_dec_ref_known(v___x_4688_, 1);
v_snd_4690_ = lean_ctor_get(v_a_4689_, 1);
v_isSharedCheck_4772_ = !lean_is_exclusive(v_a_4689_);
if (v_isSharedCheck_4772_ == 0)
{
lean_object* v_unused_4773_; 
v_unused_4773_ = lean_ctor_get(v_a_4689_, 0);
lean_dec(v_unused_4773_);
v___x_4692_ = v_a_4689_;
v_isShared_4693_ = v_isSharedCheck_4772_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_snd_4690_);
lean_dec(v_a_4689_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4772_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
size_t v_sz_4694_; lean_object* v___x_4695_; 
v_sz_4694_ = lean_array_size(v___y_4677_);
v___x_4695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(v_sz_4694_, v___x_4681_, v___y_4677_, v_a_4667_, v_snd_4690_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; lean_object* v_fst_4697_; lean_object* v_snd_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4763_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4695_, 1);
v_fst_4697_ = lean_ctor_get(v_a_4696_, 0);
v_snd_4698_ = lean_ctor_get(v_a_4696_, 1);
v_isSharedCheck_4763_ = !lean_is_exclusive(v_a_4696_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4700_ = v_a_4696_;
v_isShared_4701_ = v_isSharedCheck_4763_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_snd_4698_);
lean_inc(v_fst_4697_);
lean_dec(v_a_4696_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4763_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
size_t v_sz_4702_; lean_object* v___x_4703_; 
v_sz_4702_ = lean_array_size(v___y_4676_);
v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(v_sz_4702_, v___x_4681_, v___y_4676_, v_a_4667_, v_snd_4698_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v_fst_4705_; lean_object* v_snd_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4754_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
lean_inc(v_a_4704_);
lean_dec_ref_known(v___x_4703_, 1);
v_fst_4705_ = lean_ctor_get(v_a_4704_, 0);
v_snd_4706_ = lean_ctor_get(v_a_4704_, 1);
v_isSharedCheck_4754_ = !lean_is_exclusive(v_a_4704_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4708_ = v_a_4704_;
v_isShared_4709_ = v_isSharedCheck_4754_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_snd_4706_);
lean_inc(v_fst_4705_);
lean_dec(v_a_4704_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4754_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4710_; 
v___x_4710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_4680_, v___x_4681_, v_fst_4678_, v_a_4667_, v_snd_4706_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; lean_object* v_fst_4712_; lean_object* v_snd_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4745_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_a_4711_);
lean_dec_ref_known(v___x_4710_, 1);
v_fst_4712_ = lean_ctor_get(v_a_4711_, 0);
v_snd_4713_ = lean_ctor_get(v_a_4711_, 1);
v_isSharedCheck_4745_ = !lean_is_exclusive(v_a_4711_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4715_ = v_a_4711_;
v_isShared_4716_ = v_isSharedCheck_4745_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_snd_4713_);
lean_inc(v_fst_4712_);
lean_dec(v_a_4711_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4745_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4721_; 
v___x_4717_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__0));
v___x_4718_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__1));
v___x_4719_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4697_);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 1, v___x_4719_);
lean_ctor_set(v___x_4715_, 0, v___x_4718_);
v___x_4721_ = v___x_4715_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4718_);
lean_ctor_set(v_reuseFailAlloc_4744_, 1, v___x_4719_);
v___x_4721_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4725_; 
v___x_4722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2));
v___x_4723_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4705_);
if (v_isShared_4709_ == 0)
{
lean_ctor_set(v___x_4708_, 1, v___x_4723_);
lean_ctor_set(v___x_4708_, 0, v___x_4722_);
v___x_4725_ = v___x_4708_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4743_, 1, v___x_4723_);
v___x_4725_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4729_; 
v___x_4726_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__2));
v___x_4727_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4712_);
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 1, v___x_4727_);
lean_ctor_set(v___x_4700_, 0, v___x_4726_);
v___x_4729_ = v___x_4700_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4726_);
lean_ctor_set(v_reuseFailAlloc_4742_, 1, v___x_4727_);
v___x_4729_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
lean_object* v___x_4730_; lean_object* v___x_4732_; 
v___x_4730_ = lean_box(0);
if (v_isShared_4687_ == 0)
{
lean_ctor_set_tag(v___x_4686_, 1);
lean_ctor_set(v___x_4686_, 1, v___x_4730_);
lean_ctor_set(v___x_4686_, 0, v___x_4729_);
v___x_4732_ = v___x_4686_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4729_);
lean_ctor_set(v_reuseFailAlloc_4741_, 1, v___x_4730_);
v___x_4732_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4737_; 
v___x_4733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4725_);
lean_ctor_set(v___x_4733_, 1, v___x_4732_);
v___x_4734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4721_);
lean_ctor_set(v___x_4734_, 1, v___x_4733_);
v___x_4735_ = l_Lean_Json_mkObj(v___x_4734_);
lean_dec_ref_known(v___x_4734_, 2);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 1, v___x_4735_);
lean_ctor_set(v___x_4692_, 0, v___x_4717_);
v___x_4737_ = v___x_4692_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4740_, 1, v___x_4735_);
v___x_4737_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
lean_ctor_set(v___x_4738_, 1, v___x_4730_);
v___x_4739_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4738_, v_snd_4713_);
lean_dec_ref_known(v___x_4738_, 2);
return v___x_4739_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
lean_del_object(v___x_4708_);
lean_dec(v_fst_4705_);
lean_del_object(v___x_4700_);
lean_dec(v_fst_4697_);
lean_del_object(v___x_4692_);
lean_del_object(v___x_4686_);
v_a_4746_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4710_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4710_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
lean_del_object(v___x_4700_);
lean_dec(v_fst_4697_);
lean_del_object(v___x_4692_);
lean_del_object(v___x_4686_);
lean_dec_ref(v_fst_4678_);
v_a_4755_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4703_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4703_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
lean_del_object(v___x_4692_);
lean_del_object(v___x_4686_);
lean_dec_ref(v_fst_4678_);
lean_dec(v___y_4676_);
v_a_4764_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4695_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4695_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
}
else
{
lean_del_object(v___x_4686_);
lean_dec_ref(v_fst_4678_);
lean_dec(v___y_4677_);
lean_dec(v___y_4676_);
return v___x_4688_;
}
}
}
else
{
lean_dec_ref(v_fst_4678_);
lean_dec(v___y_4677_);
lean_dec(v___y_4676_);
return v___x_4682_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(lean_object* v_as_5534_, size_t v_sz_5535_, size_t v_i_5536_, lean_object* v_b_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_){
_start:
{
uint8_t v___x_5541_; 
v___x_5541_ = lean_usize_dec_lt(v_i_5536_, v_sz_5535_);
if (v___x_5541_ == 0)
{
lean_object* v___x_5542_; lean_object* v___x_5543_; 
v___x_5542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5542_, 0, v_b_5537_);
lean_ctor_set(v___x_5542_, 1, v___y_5539_);
v___x_5543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5543_, 0, v___x_5542_);
return v___x_5543_;
}
else
{
lean_object* v___x_5544_; lean_object* v_a_5545_; lean_object* v___x_5546_; 
v___x_5544_ = lean_box(0);
v_a_5545_ = lean_array_uget_borrowed(v_as_5534_, v_i_5536_);
lean_inc(v_a_5545_);
v___x_5546_ = l_LeanExport_dumpConstant(v_a_5545_, v___y_5538_, v___y_5539_);
if (lean_obj_tag(v___x_5546_) == 0)
{
lean_object* v_a_5547_; lean_object* v_snd_5548_; size_t v___x_5549_; size_t v___x_5550_; 
v_a_5547_ = lean_ctor_get(v___x_5546_, 0);
lean_inc(v_a_5547_);
lean_dec_ref_known(v___x_5546_, 1);
v_snd_5548_ = lean_ctor_get(v_a_5547_, 1);
lean_inc(v_snd_5548_);
lean_dec(v_a_5547_);
v___x_5549_ = ((size_t)1ULL);
v___x_5550_ = lean_usize_add(v_i_5536_, v___x_5549_);
v_i_5536_ = v___x_5550_;
v_b_5537_ = v___x_5544_;
v___y_5539_ = v_snd_5548_;
goto _start;
}
else
{
return v___x_5546_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(lean_object* v_e_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_){
_start:
{
lean_object* v___x_5556_; lean_object* v___x_5557_; size_t v_sz_5558_; size_t v___x_5559_; lean_object* v___x_5560_; 
v___x_5556_ = l_Lean_Expr_getUsedConstants(v_e_5552_);
v___x_5557_ = lean_box(0);
v_sz_5558_ = lean_array_size(v___x_5556_);
v___x_5559_ = ((size_t)0ULL);
v___x_5560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v___x_5556_, v_sz_5558_, v___x_5559_, v___x_5557_, v_a_5553_, v_a_5554_);
lean_dec_ref(v___x_5556_);
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5577_; 
v_a_5561_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5577_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5577_ == 0)
{
v___x_5563_ = v___x_5560_;
v_isShared_5564_ = v_isSharedCheck_5577_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_dec(v___x_5560_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5577_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v_snd_5565_; lean_object* v___x_5567_; uint8_t v_isShared_5568_; uint8_t v_isSharedCheck_5575_; 
v_snd_5565_ = lean_ctor_get(v_a_5561_, 1);
v_isSharedCheck_5575_ = !lean_is_exclusive(v_a_5561_);
if (v_isSharedCheck_5575_ == 0)
{
lean_object* v_unused_5576_; 
v_unused_5576_ = lean_ctor_get(v_a_5561_, 0);
lean_dec(v_unused_5576_);
v___x_5567_ = v_a_5561_;
v_isShared_5568_ = v_isSharedCheck_5575_;
goto v_resetjp_5566_;
}
else
{
lean_inc(v_snd_5565_);
lean_dec(v_a_5561_);
v___x_5567_ = lean_box(0);
v_isShared_5568_ = v_isSharedCheck_5575_;
goto v_resetjp_5566_;
}
v_resetjp_5566_:
{
lean_object* v___x_5570_; 
if (v_isShared_5568_ == 0)
{
lean_ctor_set(v___x_5567_, 0, v___x_5557_);
v___x_5570_ = v___x_5567_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v___x_5557_);
lean_ctor_set(v_reuseFailAlloc_5574_, 1, v_snd_5565_);
v___x_5570_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
lean_object* v___x_5572_; 
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 0, v___x_5570_);
v___x_5572_ = v___x_5563_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5570_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
}
else
{
return v___x_5560_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps___boxed(lean_object* v_e_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_){
_start:
{
lean_object* v_res_5582_; 
v_res_5582_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_e_5578_, v_a_5579_, v_a_5580_);
lean_dec_ref(v_a_5579_);
return v_res_5582_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg___boxed(lean_object* v_as_x27_5583_, lean_object* v_b_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_){
_start:
{
lean_object* v_res_5588_; 
v_res_5588_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5583_, v_b_5584_, v___y_5585_, v___y_5586_);
lean_dec_ref(v___y_5585_);
lean_dec(v_as_x27_5583_);
return v_res_5588_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg___boxed(lean_object* v_as_x27_5589_, lean_object* v_b_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_){
_start:
{
lean_object* v_res_5594_; 
v_res_5594_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5589_, v_b_5590_, v___y_5591_, v___y_5592_);
lean_dec_ref(v___y_5591_);
lean_dec(v_as_x27_5589_);
return v_res_5594_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2___boxed(lean_object* v_x_5595_, lean_object* v_x_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_){
_start:
{
lean_object* v_res_5600_; 
v_res_5600_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_x_5595_, v_x_5596_, v___y_5597_, v___y_5598_);
lean_dec_ref(v___y_5597_);
return v_res_5600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0___boxed(lean_object* v_as_5601_, lean_object* v_sz_5602_, lean_object* v_i_5603_, lean_object* v_b_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_){
_start:
{
size_t v_sz_boxed_5608_; size_t v_i_boxed_5609_; lean_object* v_res_5610_; 
v_sz_boxed_5608_ = lean_unbox_usize(v_sz_5602_);
lean_dec(v_sz_5602_);
v_i_boxed_5609_ = lean_unbox_usize(v_i_5603_);
lean_dec(v_i_5603_);
v_res_5610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v_as_5601_, v_sz_boxed_5608_, v_i_boxed_5609_, v_b_5604_, v___y_5605_, v___y_5606_);
lean_dec_ref(v___y_5605_);
lean_dec_ref(v_as_5601_);
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___boxed(lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_){
_start:
{
lean_object* v_res_5614_; 
v_res_5614_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_5611_, v_a_5612_);
lean_dec_ref(v_a_5611_);
return v_res_5614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object* v_as_5615_, lean_object* v_sz_5616_, lean_object* v_i_5617_, lean_object* v_b_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_){
_start:
{
size_t v_sz_boxed_5622_; size_t v_i_boxed_5623_; lean_object* v_res_5624_; 
v_sz_boxed_5622_ = lean_unbox_usize(v_sz_5616_);
lean_dec(v_sz_5616_);
v_i_boxed_5623_ = lean_unbox_usize(v_i_5617_);
lean_dec(v_i_5617_);
v_res_5624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(v_as_5615_, v_sz_boxed_5622_, v_i_boxed_5623_, v_b_5618_, v___y_5619_, v___y_5620_);
lean_dec_ref(v___y_5619_);
lean_dec_ref(v_as_5615_);
return v_res_5624_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object* v_e_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_){
_start:
{
lean_object* v_res_5629_; 
v_res_5629_ = l_LeanExport_dumpExpr(v_e_5625_, v_a_5626_, v_a_5627_);
lean_dec_ref(v_a_5626_);
return v_res_5629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object* v_as_5630_, lean_object* v_sz_5631_, lean_object* v_i_5632_, lean_object* v_b_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_){
_start:
{
size_t v_sz_boxed_5637_; size_t v_i_boxed_5638_; lean_object* v_res_5639_; 
v_sz_boxed_5637_ = lean_unbox_usize(v_sz_5631_);
lean_dec(v_sz_5631_);
v_i_boxed_5638_ = lean_unbox_usize(v_i_5632_);
lean_dec(v_i_5632_);
v_res_5639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_as_5630_, v_sz_boxed_5637_, v_i_boxed_5638_, v_b_5633_, v___y_5634_, v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec_ref(v_as_5630_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object* v_as_5640_, lean_object* v_sz_5641_, lean_object* v_i_5642_, lean_object* v_b_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_){
_start:
{
size_t v_sz_boxed_5647_; size_t v_i_boxed_5648_; lean_object* v_res_5649_; 
v_sz_boxed_5647_ = lean_unbox_usize(v_sz_5641_);
lean_dec(v_sz_5641_);
v_i_boxed_5648_ = lean_unbox_usize(v_i_5642_);
lean_dec(v_i_5642_);
v_res_5649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(v_as_5640_, v_sz_boxed_5647_, v_i_boxed_5648_, v_b_5643_, v___y_5644_, v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec_ref(v_as_5640_);
return v_res_5649_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object* v_rule_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_){
_start:
{
lean_object* v_res_5654_; 
v_res_5654_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_rule_5650_, v_a_5651_, v_a_5652_);
lean_dec_ref(v_a_5651_);
return v_res_5654_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_){
_start:
{
lean_object* v_res_5658_; 
v_res_5658_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_5655_, v_a_5656_);
lean_dec_ref(v_a_5655_);
return v_res_5658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object* v_sz_5659_, lean_object* v_i_5660_, lean_object* v_bs_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_){
_start:
{
size_t v_sz_boxed_5665_; size_t v_i_boxed_5666_; lean_object* v_res_5667_; 
v_sz_boxed_5665_ = lean_unbox_usize(v_sz_5659_);
lean_dec(v_sz_5659_);
v_i_boxed_5666_ = lean_unbox_usize(v_i_5660_);
lean_dec(v_i_5660_);
v_res_5667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(v_sz_boxed_5665_, v_i_boxed_5666_, v_bs_5661_, v___y_5662_, v___y_5663_);
lean_dec_ref(v___y_5662_);
return v_res_5667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object* v_sz_5668_, lean_object* v_i_5669_, lean_object* v_bs_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
size_t v_sz_boxed_5674_; size_t v_i_boxed_5675_; lean_object* v_res_5676_; 
v_sz_boxed_5674_ = lean_unbox_usize(v_sz_5668_);
lean_dec(v_sz_5668_);
v_i_boxed_5675_ = lean_unbox_usize(v_i_5669_);
lean_dec(v_i_5669_);
v_res_5676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(v_sz_boxed_5674_, v_i_boxed_5675_, v_bs_5670_, v___y_5671_, v___y_5672_);
lean_dec_ref(v___y_5671_);
return v_res_5676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object* v_sz_5677_, lean_object* v_i_5678_, lean_object* v_bs_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_){
_start:
{
size_t v_sz_boxed_5683_; size_t v_i_boxed_5684_; lean_object* v_res_5685_; 
v_sz_boxed_5683_ = lean_unbox_usize(v_sz_5677_);
lean_dec(v_sz_5677_);
v_i_boxed_5684_ = lean_unbox_usize(v_i_5678_);
lean_dec(v_i_5678_);
v_res_5685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_boxed_5683_, v_i_boxed_5684_, v_bs_5679_, v___y_5680_, v___y_5681_);
lean_dec_ref(v___y_5680_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object* v___x_5686_, lean_object* v_as_x27_5687_, lean_object* v_b_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_){
_start:
{
uint8_t v___x_173317__boxed_5692_; lean_object* v_res_5693_; 
v___x_173317__boxed_5692_ = lean_unbox(v___x_5686_);
v_res_5693_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_173317__boxed_5692_, v_as_x27_5687_, v_b_5688_, v___y_5689_, v___y_5690_);
lean_dec_ref(v___y_5689_);
lean_dec(v_as_x27_5687_);
return v_res_5693_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___boxed(lean_object* v___x_5694_, lean_object* v_val_5695_, lean_object* v_as_x27_5696_, lean_object* v_b_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_){
_start:
{
uint8_t v___x_173417__boxed_5701_; lean_object* v_res_5702_; 
v___x_173417__boxed_5701_ = lean_unbox(v___x_5694_);
v_res_5702_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_173417__boxed_5701_, v_val_5695_, v_as_x27_5696_, v_b_5697_, v___y_5698_, v___y_5699_);
lean_dec_ref(v___y_5698_);
lean_dec(v_as_x27_5696_);
lean_dec_ref(v_val_5695_);
return v_res_5702_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux___boxed(lean_object* v_e_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_){
_start:
{
lean_object* v_res_5707_; 
v_res_5707_ = l_LeanExport_dumpExprAux(v_e_5703_, v_a_5704_, v_a_5705_);
lean_dec_ref(v_a_5704_);
return v_res_5707_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant___boxed(lean_object* v_c_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_){
_start:
{
lean_object* v_res_5712_; 
v_res_5712_ = l_LeanExport_dumpConstant(v_c_5708_, v_a_5709_, v_a_5710_);
lean_dec_ref(v_a_5709_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(uint8_t v___x_5713_, lean_object* v_as_5714_, lean_object* v_as_x27_5715_, lean_object* v_b_5716_, lean_object* v_a_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_){
_start:
{
lean_object* v___x_5721_; 
v___x_5721_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_5713_, v_as_x27_5715_, v_b_5716_, v___y_5718_, v___y_5719_);
return v___x_5721_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___boxed(lean_object* v___x_5722_, lean_object* v_as_5723_, lean_object* v_as_x27_5724_, lean_object* v_b_5725_, lean_object* v_a_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_){
_start:
{
uint8_t v___x_177938__boxed_5730_; lean_object* v_res_5731_; 
v___x_177938__boxed_5730_ = lean_unbox(v___x_5722_);
v_res_5731_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(v___x_177938__boxed_5730_, v_as_5723_, v_as_x27_5724_, v_b_5725_, v_a_5726_, v___y_5727_, v___y_5728_);
lean_dec_ref(v___y_5727_);
lean_dec(v_as_x27_5724_);
lean_dec(v_as_5723_);
return v_res_5731_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(uint8_t v___y_5732_, uint8_t v___x_5733_, lean_object* v_as_5734_, lean_object* v_as_x27_5735_, lean_object* v_b_5736_, lean_object* v_a_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_){
_start:
{
lean_object* v___x_5741_; 
v___x_5741_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_5732_, v___x_5733_, v_as_x27_5735_, v_b_5736_, v___y_5738_, v___y_5739_);
return v___x_5741_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___boxed(lean_object* v___y_5742_, lean_object* v___x_5743_, lean_object* v_as_5744_, lean_object* v_as_x27_5745_, lean_object* v_b_5746_, lean_object* v_a_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_){
_start:
{
uint8_t v___y_177955__boxed_5751_; uint8_t v___x_177956__boxed_5752_; lean_object* v_res_5753_; 
v___y_177955__boxed_5751_ = lean_unbox(v___y_5742_);
v___x_177956__boxed_5752_ = lean_unbox(v___x_5743_);
v_res_5753_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(v___y_177955__boxed_5751_, v___x_177956__boxed_5752_, v_as_5744_, v_as_x27_5745_, v_b_5746_, v_a_5747_, v___y_5748_, v___y_5749_);
lean_dec_ref(v___y_5748_);
lean_dec(v_as_x27_5745_);
lean_dec(v_as_5744_);
return v_res_5753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(lean_object* v_00_u03b4_5754_, lean_object* v_t_5755_, lean_object* v_k_5756_){
_start:
{
lean_object* v___x_5757_; 
v___x_5757_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_5755_, v_k_5756_);
return v___x_5757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___boxed(lean_object* v_00_u03b4_5758_, lean_object* v_t_5759_, lean_object* v_k_5760_){
_start:
{
lean_object* v_res_5761_; 
v_res_5761_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(v_00_u03b4_5758_, v_t_5759_, v_k_5760_);
lean_dec(v_k_5760_);
lean_dec(v_t_5759_);
return v_res_5761_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(uint8_t v___x_5762_, lean_object* v_val_5763_, lean_object* v_as_5764_, lean_object* v_as_x27_5765_, lean_object* v_b_5766_, lean_object* v_a_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_){
_start:
{
lean_object* v___x_5771_; 
v___x_5771_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_5762_, v_val_5763_, v_as_x27_5765_, v_b_5766_, v___y_5768_, v___y_5769_);
return v___x_5771_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___boxed(lean_object* v___x_5772_, lean_object* v_val_5773_, lean_object* v_as_5774_, lean_object* v_as_x27_5775_, lean_object* v_b_5776_, lean_object* v_a_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_){
_start:
{
uint8_t v___x_177977__boxed_5781_; lean_object* v_res_5782_; 
v___x_177977__boxed_5781_ = lean_unbox(v___x_5772_);
v_res_5782_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(v___x_177977__boxed_5781_, v_val_5773_, v_as_5774_, v_as_x27_5775_, v_b_5776_, v_a_5777_, v___y_5778_, v___y_5779_);
lean_dec_ref(v___y_5778_);
lean_dec(v_as_x27_5775_);
lean_dec(v_as_5774_);
lean_dec_ref(v_val_5773_);
return v_res_5782_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(lean_object* v_as_5783_, lean_object* v_as_x27_5784_, lean_object* v_b_5785_, lean_object* v_a_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_){
_start:
{
lean_object* v___x_5790_; 
v___x_5790_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5784_, v_b_5785_, v___y_5787_, v___y_5788_);
return v___x_5790_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___boxed(lean_object* v_as_5791_, lean_object* v_as_x27_5792_, lean_object* v_b_5793_, lean_object* v_a_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_){
_start:
{
lean_object* v_res_5798_; 
v_res_5798_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(v_as_5791_, v_as_x27_5792_, v_b_5793_, v_a_5794_, v___y_5795_, v___y_5796_);
lean_dec_ref(v___y_5795_);
lean_dec(v_as_x27_5792_);
lean_dec(v_as_5791_);
return v_res_5798_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(lean_object* v_as_5799_, lean_object* v_as_x27_5800_, lean_object* v_b_5801_, lean_object* v_a_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_){
_start:
{
lean_object* v___x_5806_; 
v___x_5806_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5800_, v_b_5801_, v___y_5803_, v___y_5804_);
return v___x_5806_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___boxed(lean_object* v_as_5807_, lean_object* v_as_x27_5808_, lean_object* v_b_5809_, lean_object* v_a_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_){
_start:
{
lean_object* v_res_5814_; 
v_res_5814_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(v_as_5807_, v_as_x27_5808_, v_b_5809_, v_a_5810_, v___y_5811_, v___y_5812_);
lean_dec_ref(v___y_5811_);
lean_dec(v_as_x27_5808_);
lean_dec(v_as_5807_);
return v_res_5814_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1(void){
_start:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; 
v___x_5816_ = l_Lean_versionString;
v___x_5817_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5817_, 0, v___x_5816_);
return v___x_5817_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2(void){
_start:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; 
v___x_5818_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1);
v___x_5819_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0));
v___x_5820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5820_, 0, v___x_5819_);
lean_ctor_set(v___x_5820_, 1, v___x_5818_);
return v___x_5820_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4(void){
_start:
{
lean_object* v___x_5822_; lean_object* v___x_5823_; 
v___x_5822_ = l_Lean_githash;
v___x_5823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5823_, 0, v___x_5822_);
return v___x_5823_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5(void){
_start:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5824_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4);
v___x_5825_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3));
v___x_5826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5826_, 0, v___x_5825_);
lean_ctor_set(v___x_5826_, 1, v___x_5824_);
return v___x_5826_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6(void){
_start:
{
lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; 
v___x_5827_ = lean_box(0);
v___x_5828_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5);
v___x_5829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5829_, 0, v___x_5828_);
lean_ctor_set(v___x_5829_, 1, v___x_5827_);
return v___x_5829_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7(void){
_start:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5830_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6);
v___x_5831_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2);
v___x_5832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5831_);
lean_ctor_set(v___x_5832_, 1, v___x_5830_);
return v___x_5832_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8(void){
_start:
{
lean_object* v___x_5833_; lean_object* v_leanMeta_5834_; 
v___x_5833_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7);
v_leanMeta_5834_ = l_Lean_Json_mkObj(v___x_5833_);
return v_leanMeta_5834_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17(void){
_start:
{
lean_object* v___x_5853_; lean_object* v_exporterMeta_5854_; 
v___x_5853_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16));
v_exporterMeta_5854_ = l_Lean_Json_mkObj(v___x_5853_);
return v_exporterMeta_5854_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18(void){
_start:
{
lean_object* v___x_5855_; lean_object* v_formatMeta_5856_; 
v___x_5855_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15));
v_formatMeta_5856_ = l_Lean_Json_mkObj(v___x_5855_);
return v_formatMeta_5856_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21(void){
_start:
{
lean_object* v_exporterMeta_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; 
v_exporterMeta_5859_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17);
v___x_5860_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20));
v___x_5861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5861_, 0, v___x_5860_);
lean_ctor_set(v___x_5861_, 1, v_exporterMeta_5859_);
return v___x_5861_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23(void){
_start:
{
lean_object* v_leanMeta_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; 
v_leanMeta_5863_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8);
v___x_5864_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22));
v___x_5865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5864_);
lean_ctor_set(v___x_5865_, 1, v_leanMeta_5863_);
return v___x_5865_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25(void){
_start:
{
lean_object* v_formatMeta_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; 
v_formatMeta_5867_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18);
v___x_5868_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24));
v___x_5869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5869_, 0, v___x_5868_);
lean_ctor_set(v___x_5869_, 1, v_formatMeta_5867_);
return v___x_5869_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26(void){
_start:
{
lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; 
v___x_5870_ = lean_box(0);
v___x_5871_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25);
v___x_5872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5872_, 0, v___x_5871_);
lean_ctor_set(v___x_5872_, 1, v___x_5870_);
return v___x_5872_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27(void){
_start:
{
lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; 
v___x_5873_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26);
v___x_5874_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23);
v___x_5875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5874_);
lean_ctor_set(v___x_5875_, 1, v___x_5873_);
return v___x_5875_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28(void){
_start:
{
lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; 
v___x_5876_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27);
v___x_5877_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21);
v___x_5878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5877_);
lean_ctor_set(v___x_5878_, 1, v___x_5876_);
return v___x_5878_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29(void){
_start:
{
lean_object* v___x_5879_; lean_object* v___x_5880_; 
v___x_5879_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28);
v___x_5880_ = l_Lean_Json_mkObj(v___x_5879_);
return v___x_5880_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30(void){
_start:
{
lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; 
v___x_5881_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29);
v___x_5882_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19));
v___x_5883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5883_, 0, v___x_5882_);
lean_ctor_set(v___x_5883_, 1, v___x_5881_);
return v___x_5883_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31(void){
_start:
{
lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; 
v___x_5884_ = lean_box(0);
v___x_5885_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30);
v___x_5886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5886_, 0, v___x_5885_);
lean_ctor_set(v___x_5886_, 1, v___x_5884_);
return v___x_5886_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32(void){
_start:
{
lean_object* v___x_5887_; lean_object* v___x_5888_; 
v___x_5887_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31);
v___x_5888_ = l_Lean_Json_mkObj(v___x_5887_);
return v___x_5888_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata(void){
_start:
{
lean_object* v___x_5889_; 
v___x_5889_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32);
return v___x_5889_;
}
}
static lean_object* _init_l_LeanExport_dumpMetadata___redArg___closed__0(void){
_start:
{
lean_object* v___x_5890_; lean_object* v___x_5891_; 
v___x_5890_ = l___private_LeanExport_Basic_0__LeanExport_exportMetadata;
v___x_5891_ = l_Lean_Json_compress(v___x_5890_);
return v___x_5891_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg(lean_object* v_a_5892_){
_start:
{
lean_object* v___x_5894_; lean_object* v___x_5895_; 
v___x_5894_ = lean_obj_once(&l_LeanExport_dumpMetadata___redArg___closed__0, &l_LeanExport_dumpMetadata___redArg___closed__0_once, _init_l_LeanExport_dumpMetadata___redArg___closed__0);
v___x_5895_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_5894_);
if (lean_obj_tag(v___x_5895_) == 0)
{
lean_object* v_a_5896_; lean_object* v___x_5898_; uint8_t v_isShared_5899_; uint8_t v_isSharedCheck_5904_; 
v_a_5896_ = lean_ctor_get(v___x_5895_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5895_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5898_ = v___x_5895_;
v_isShared_5899_ = v_isSharedCheck_5904_;
goto v_resetjp_5897_;
}
else
{
lean_inc(v_a_5896_);
lean_dec(v___x_5895_);
v___x_5898_ = lean_box(0);
v_isShared_5899_ = v_isSharedCheck_5904_;
goto v_resetjp_5897_;
}
v_resetjp_5897_:
{
lean_object* v___x_5900_; lean_object* v___x_5902_; 
v___x_5900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5900_, 0, v_a_5896_);
lean_ctor_set(v___x_5900_, 1, v_a_5892_);
if (v_isShared_5899_ == 0)
{
lean_ctor_set(v___x_5898_, 0, v___x_5900_);
v___x_5902_ = v___x_5898_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v___x_5900_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
}
else
{
lean_object* v_a_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5912_; 
lean_dec_ref(v_a_5892_);
v_a_5905_ = lean_ctor_get(v___x_5895_, 0);
v_isSharedCheck_5912_ = !lean_is_exclusive(v___x_5895_);
if (v_isSharedCheck_5912_ == 0)
{
v___x_5907_ = v___x_5895_;
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_a_5905_);
lean_dec(v___x_5895_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5910_; 
if (v_isShared_5908_ == 0)
{
v___x_5910_ = v___x_5907_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_a_5905_);
v___x_5910_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
return v___x_5910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg___boxed(lean_object* v_a_5913_, lean_object* v_a_5914_){
_start:
{
lean_object* v_res_5915_; 
v_res_5915_ = l_LeanExport_dumpMetadata___redArg(v_a_5913_);
return v_res_5915_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata(lean_object* v_a_5916_, lean_object* v_a_5917_){
_start:
{
lean_object* v___x_5919_; 
v___x_5919_ = l_LeanExport_dumpMetadata___redArg(v_a_5917_);
return v___x_5919_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___boxed(lean_object* v_a_5920_, lean_object* v_a_5921_, lean_object* v_a_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l_LeanExport_dumpMetadata(v_a_5920_, v_a_5921_);
lean_dec_ref(v_a_5920_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(lean_object* v_as_x27_5924_, lean_object* v_b_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_){
_start:
{
if (lean_obj_tag(v_as_x27_5924_) == 0)
{
lean_object* v___x_5929_; lean_object* v___x_5930_; 
v___x_5929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5929_, 0, v_b_5925_);
lean_ctor_set(v___x_5929_, 1, v___y_5927_);
v___x_5930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5929_);
return v___x_5930_;
}
else
{
lean_object* v_head_5931_; lean_object* v_tail_5932_; lean_object* v_visitedNames_5933_; lean_object* v_visitedLevels_5934_; lean_object* v_visitedExprs_5935_; lean_object* v_visitedConstants_5936_; uint8_t v_exportMData_5937_; uint8_t v_exportUnsafe_5938_; uint8_t v_ignoreMissing_5939_; lean_object* v_recursorMap_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5953_; 
v_head_5931_ = lean_ctor_get(v_as_x27_5924_, 0);
v_tail_5932_ = lean_ctor_get(v_as_x27_5924_, 1);
v_visitedNames_5933_ = lean_ctor_get(v___y_5927_, 0);
v_visitedLevels_5934_ = lean_ctor_get(v___y_5927_, 1);
v_visitedExprs_5935_ = lean_ctor_get(v___y_5927_, 2);
v_visitedConstants_5936_ = lean_ctor_get(v___y_5927_, 3);
v_exportMData_5937_ = lean_ctor_get_uint8(v___y_5927_, sizeof(void*)*6);
v_exportUnsafe_5938_ = lean_ctor_get_uint8(v___y_5927_, sizeof(void*)*6 + 1);
v_ignoreMissing_5939_ = lean_ctor_get_uint8(v___y_5927_, sizeof(void*)*6 + 2);
v_recursorMap_5940_ = lean_ctor_get(v___y_5927_, 5);
v_isSharedCheck_5953_ = !lean_is_exclusive(v___y_5927_);
if (v_isSharedCheck_5953_ == 0)
{
lean_object* v_unused_5954_; 
v_unused_5954_ = lean_ctor_get(v___y_5927_, 4);
lean_dec(v_unused_5954_);
v___x_5942_ = v___y_5927_;
v_isShared_5943_ = v_isSharedCheck_5953_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_recursorMap_5940_);
lean_inc(v_visitedConstants_5936_);
lean_inc(v_visitedExprs_5935_);
lean_inc(v_visitedLevels_5934_);
lean_inc(v_visitedNames_5933_);
lean_dec(v___y_5927_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5953_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5947_; 
v___x_5944_ = lean_box(0);
v___x_5945_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 4, v___x_5945_);
v___x_5947_ = v___x_5942_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_visitedNames_5933_);
lean_ctor_set(v_reuseFailAlloc_5952_, 1, v_visitedLevels_5934_);
lean_ctor_set(v_reuseFailAlloc_5952_, 2, v_visitedExprs_5935_);
lean_ctor_set(v_reuseFailAlloc_5952_, 3, v_visitedConstants_5936_);
lean_ctor_set(v_reuseFailAlloc_5952_, 4, v___x_5945_);
lean_ctor_set(v_reuseFailAlloc_5952_, 5, v_recursorMap_5940_);
lean_ctor_set_uint8(v_reuseFailAlloc_5952_, sizeof(void*)*6, v_exportMData_5937_);
lean_ctor_set_uint8(v_reuseFailAlloc_5952_, sizeof(void*)*6 + 1, v_exportUnsafe_5938_);
lean_ctor_set_uint8(v_reuseFailAlloc_5952_, sizeof(void*)*6 + 2, v_ignoreMissing_5939_);
v___x_5947_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
lean_object* v___x_5948_; 
lean_inc(v_head_5931_);
v___x_5948_ = l_LeanExport_dumpConstant(v_head_5931_, v___y_5926_, v___x_5947_);
if (lean_obj_tag(v___x_5948_) == 0)
{
lean_object* v_a_5949_; lean_object* v_snd_5950_; 
v_a_5949_ = lean_ctor_get(v___x_5948_, 0);
lean_inc(v_a_5949_);
lean_dec_ref_known(v___x_5948_, 1);
v_snd_5950_ = lean_ctor_get(v_a_5949_, 1);
lean_inc(v_snd_5950_);
lean_dec(v_a_5949_);
v_as_x27_5924_ = v_tail_5932_;
v_b_5925_ = v___x_5944_;
v___y_5927_ = v_snd_5950_;
goto _start;
}
else
{
return v___x_5948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg___boxed(lean_object* v_as_x27_5955_, lean_object* v_b_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_){
_start:
{
lean_object* v_res_5960_; 
v_res_5960_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_5955_, v_b_5956_, v___y_5957_, v___y_5958_);
lean_dec_ref(v___y_5957_);
lean_dec(v_as_x27_5955_);
return v_res_5960_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0(lean_object* v_env_5961_, lean_object* v_cliOptions_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_){
_start:
{
lean_object* v___x_5967_; 
v___x_5967_ = l_LeanExport_initState(v_env_5961_, v_cliOptions_5962_, v___y_5964_, v___y_5965_);
if (lean_obj_tag(v___x_5967_) == 0)
{
lean_object* v_a_5968_; lean_object* v_snd_5969_; lean_object* v___x_5970_; 
v_a_5968_ = lean_ctor_get(v___x_5967_, 0);
lean_inc(v_a_5968_);
lean_dec_ref_known(v___x_5967_, 1);
v_snd_5969_ = lean_ctor_get(v_a_5968_, 1);
lean_inc(v_snd_5969_);
lean_dec(v_a_5968_);
v___x_5970_ = l_LeanExport_dumpMetadata___redArg(v_snd_5969_);
if (lean_obj_tag(v___x_5970_) == 0)
{
lean_object* v_a_5971_; lean_object* v_snd_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; 
v_a_5971_ = lean_ctor_get(v___x_5970_, 0);
lean_inc(v_a_5971_);
lean_dec_ref_known(v___x_5970_, 1);
v_snd_5972_ = lean_ctor_get(v_a_5971_, 1);
lean_inc(v_snd_5972_);
lean_dec(v_a_5971_);
v___x_5973_ = lean_box(0);
v___x_5974_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v___y_5963_, v___x_5973_, v___y_5964_, v_snd_5972_);
if (lean_obj_tag(v___x_5974_) == 0)
{
lean_object* v_a_5975_; lean_object* v___x_5977_; uint8_t v_isShared_5978_; uint8_t v_isSharedCheck_5991_; 
v_a_5975_ = lean_ctor_get(v___x_5974_, 0);
v_isSharedCheck_5991_ = !lean_is_exclusive(v___x_5974_);
if (v_isSharedCheck_5991_ == 0)
{
v___x_5977_ = v___x_5974_;
v_isShared_5978_ = v_isSharedCheck_5991_;
goto v_resetjp_5976_;
}
else
{
lean_inc(v_a_5975_);
lean_dec(v___x_5974_);
v___x_5977_ = lean_box(0);
v_isShared_5978_ = v_isSharedCheck_5991_;
goto v_resetjp_5976_;
}
v_resetjp_5976_:
{
lean_object* v_snd_5979_; lean_object* v___x_5981_; uint8_t v_isShared_5982_; uint8_t v_isSharedCheck_5989_; 
v_snd_5979_ = lean_ctor_get(v_a_5975_, 1);
v_isSharedCheck_5989_ = !lean_is_exclusive(v_a_5975_);
if (v_isSharedCheck_5989_ == 0)
{
lean_object* v_unused_5990_; 
v_unused_5990_ = lean_ctor_get(v_a_5975_, 0);
lean_dec(v_unused_5990_);
v___x_5981_ = v_a_5975_;
v_isShared_5982_ = v_isSharedCheck_5989_;
goto v_resetjp_5980_;
}
else
{
lean_inc(v_snd_5979_);
lean_dec(v_a_5975_);
v___x_5981_ = lean_box(0);
v_isShared_5982_ = v_isSharedCheck_5989_;
goto v_resetjp_5980_;
}
v_resetjp_5980_:
{
lean_object* v___x_5984_; 
if (v_isShared_5982_ == 0)
{
lean_ctor_set(v___x_5981_, 0, v___x_5973_);
v___x_5984_ = v___x_5981_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_5988_; 
v_reuseFailAlloc_5988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5988_, 0, v___x_5973_);
lean_ctor_set(v_reuseFailAlloc_5988_, 1, v_snd_5979_);
v___x_5984_ = v_reuseFailAlloc_5988_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
lean_object* v___x_5986_; 
if (v_isShared_5978_ == 0)
{
lean_ctor_set(v___x_5977_, 0, v___x_5984_);
v___x_5986_ = v___x_5977_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5987_; 
v_reuseFailAlloc_5987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5987_, 0, v___x_5984_);
v___x_5986_ = v_reuseFailAlloc_5987_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
return v___x_5986_;
}
}
}
}
}
else
{
return v___x_5974_;
}
}
else
{
return v___x_5970_;
}
}
else
{
return v___x_5967_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0___boxed(lean_object* v_env_5992_, lean_object* v_cliOptions_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_){
_start:
{
lean_object* v_res_5998_; 
v_res_5998_ = l_LeanExport_dumpEnv___lam__0(v_env_5992_, v_cliOptions_5993_, v___y_5994_, v___y_5995_, v___y_5996_);
lean_dec_ref(v___y_5995_);
lean_dec(v___y_5994_);
lean_dec(v_cliOptions_5993_);
return v_res_5998_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___lam__0(lean_object* v_es_5999_, lean_object* v_a_6000_, lean_object* v_b_6001_){
_start:
{
lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_6002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6002_, 0, v_a_6000_);
lean_ctor_set(v___x_6002_, 1, v_b_6001_);
v___x_6003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
lean_ctor_set(v___x_6003_, 1, v_es_5999_);
return v___x_6003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(lean_object* v_f_6004_, lean_object* v_x_6005_, lean_object* v_x_6006_){
_start:
{
if (lean_obj_tag(v_x_6006_) == 0)
{
lean_dec(v_f_6004_);
return v_x_6005_;
}
else
{
lean_object* v_key_6007_; lean_object* v_value_6008_; lean_object* v_tail_6009_; lean_object* v___x_6010_; 
v_key_6007_ = lean_ctor_get(v_x_6006_, 0);
lean_inc(v_key_6007_);
v_value_6008_ = lean_ctor_get(v_x_6006_, 1);
lean_inc(v_value_6008_);
v_tail_6009_ = lean_ctor_get(v_x_6006_, 2);
lean_inc(v_tail_6009_);
lean_dec_ref_known(v_x_6006_, 3);
lean_inc(v_f_6004_);
v___x_6010_ = lean_apply_3(v_f_6004_, v_x_6005_, v_key_6007_, v_value_6008_);
v_x_6005_ = v___x_6010_;
v_x_6006_ = v_tail_6009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(lean_object* v_f_6012_, lean_object* v_as_6013_, size_t v_i_6014_, size_t v_stop_6015_, lean_object* v_b_6016_){
_start:
{
uint8_t v___x_6017_; 
v___x_6017_ = lean_usize_dec_eq(v_i_6014_, v_stop_6015_);
if (v___x_6017_ == 0)
{
lean_object* v___x_6018_; lean_object* v___x_6019_; size_t v___x_6020_; size_t v___x_6021_; 
v___x_6018_ = lean_array_uget_borrowed(v_as_6013_, v_i_6014_);
lean_inc(v___x_6018_);
lean_inc(v_f_6012_);
v___x_6019_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(v_f_6012_, v_b_6016_, v___x_6018_);
v___x_6020_ = ((size_t)1ULL);
v___x_6021_ = lean_usize_add(v_i_6014_, v___x_6020_);
v_i_6014_ = v___x_6021_;
v_b_6016_ = v___x_6019_;
goto _start;
}
else
{
lean_dec(v_f_6012_);
return v_b_6016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_f_6023_, lean_object* v_as_6024_, lean_object* v_i_6025_, lean_object* v_stop_6026_, lean_object* v_b_6027_){
_start:
{
size_t v_i_boxed_6028_; size_t v_stop_boxed_6029_; lean_object* v_res_6030_; 
v_i_boxed_6028_ = lean_unbox_usize(v_i_6025_);
lean_dec(v_i_6025_);
v_stop_boxed_6029_ = lean_unbox_usize(v_stop_6026_);
lean_dec(v_stop_6026_);
v_res_6030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6023_, v_as_6024_, v_i_boxed_6028_, v_stop_boxed_6029_, v_b_6027_);
lean_dec_ref(v_as_6024_);
return v_res_6030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0(lean_object* v_f_6031_, lean_object* v_x1_6032_, lean_object* v_x2_6033_, lean_object* v_x3_6034_){
_start:
{
lean_object* v___x_6035_; 
v___x_6035_ = lean_apply_3(v_f_6031_, v_x1_6032_, v_x2_6033_, v_x3_6034_);
return v___x_6035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(lean_object* v_f_6036_, lean_object* v_keys_6037_, lean_object* v_vals_6038_, lean_object* v_i_6039_, lean_object* v_acc_6040_){
_start:
{
lean_object* v___x_6041_; uint8_t v___x_6042_; 
v___x_6041_ = lean_array_get_size(v_keys_6037_);
v___x_6042_ = lean_nat_dec_lt(v_i_6039_, v___x_6041_);
if (v___x_6042_ == 0)
{
lean_dec(v_i_6039_);
lean_dec(v_f_6036_);
return v_acc_6040_;
}
else
{
lean_object* v_k_6043_; lean_object* v_v_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; 
v_k_6043_ = lean_array_fget_borrowed(v_keys_6037_, v_i_6039_);
v_v_6044_ = lean_array_fget_borrowed(v_vals_6038_, v_i_6039_);
lean_inc(v_f_6036_);
lean_inc(v_v_6044_);
lean_inc(v_k_6043_);
v___x_6045_ = lean_apply_3(v_f_6036_, v_acc_6040_, v_k_6043_, v_v_6044_);
v___x_6046_ = lean_unsigned_to_nat(1u);
v___x_6047_ = lean_nat_add(v_i_6039_, v___x_6046_);
lean_dec(v_i_6039_);
v_i_6039_ = v___x_6047_;
v_acc_6040_ = v___x_6045_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg___boxed(lean_object* v_f_6049_, lean_object* v_keys_6050_, lean_object* v_vals_6051_, lean_object* v_i_6052_, lean_object* v_acc_6053_){
_start:
{
lean_object* v_res_6054_; 
v_res_6054_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6049_, v_keys_6050_, v_vals_6051_, v_i_6052_, v_acc_6053_);
lean_dec_ref(v_vals_6051_);
lean_dec_ref(v_keys_6050_);
return v_res_6054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(lean_object* v_f_6055_, lean_object* v_as_6056_, size_t v_i_6057_, size_t v_stop_6058_, lean_object* v_b_6059_){
_start:
{
lean_object* v___y_6061_; uint8_t v___x_6065_; 
v___x_6065_ = lean_usize_dec_eq(v_i_6057_, v_stop_6058_);
if (v___x_6065_ == 0)
{
lean_object* v___x_6066_; 
v___x_6066_ = lean_array_uget_borrowed(v_as_6056_, v_i_6057_);
switch(lean_obj_tag(v___x_6066_))
{
case 0:
{
lean_object* v_key_6067_; lean_object* v_val_6068_; lean_object* v___x_6069_; 
v_key_6067_ = lean_ctor_get(v___x_6066_, 0);
v_val_6068_ = lean_ctor_get(v___x_6066_, 1);
lean_inc(v_f_6055_);
lean_inc(v_val_6068_);
lean_inc(v_key_6067_);
v___x_6069_ = lean_apply_3(v_f_6055_, v_b_6059_, v_key_6067_, v_val_6068_);
v___y_6061_ = v___x_6069_;
goto v___jp_6060_;
}
case 1:
{
lean_object* v_node_6070_; lean_object* v___x_6071_; 
v_node_6070_ = lean_ctor_get(v___x_6066_, 0);
lean_inc(v_f_6055_);
v___x_6071_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6055_, v_node_6070_, v_b_6059_);
v___y_6061_ = v___x_6071_;
goto v___jp_6060_;
}
default: 
{
v___y_6061_ = v_b_6059_;
goto v___jp_6060_;
}
}
}
else
{
lean_dec(v_f_6055_);
return v_b_6059_;
}
v___jp_6060_:
{
size_t v___x_6062_; size_t v___x_6063_; 
v___x_6062_ = ((size_t)1ULL);
v___x_6063_ = lean_usize_add(v_i_6057_, v___x_6062_);
v_i_6057_ = v___x_6063_;
v_b_6059_ = v___y_6061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_f_6072_, lean_object* v_x_6073_, lean_object* v_x_6074_){
_start:
{
if (lean_obj_tag(v_x_6073_) == 0)
{
lean_object* v_es_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; uint8_t v___x_6078_; 
v_es_6075_ = lean_ctor_get(v_x_6073_, 0);
v___x_6076_ = lean_unsigned_to_nat(0u);
v___x_6077_ = lean_array_get_size(v_es_6075_);
v___x_6078_ = lean_nat_dec_lt(v___x_6076_, v___x_6077_);
if (v___x_6078_ == 0)
{
lean_dec(v_f_6072_);
return v_x_6074_;
}
else
{
size_t v___x_6079_; size_t v___x_6080_; lean_object* v___x_6081_; 
v___x_6079_ = ((size_t)0ULL);
v___x_6080_ = lean_usize_of_nat(v___x_6077_);
v___x_6081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6072_, v_es_6075_, v___x_6079_, v___x_6080_, v_x_6074_);
return v___x_6081_;
}
}
else
{
lean_object* v_ks_6082_; lean_object* v_vs_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; 
v_ks_6082_ = lean_ctor_get(v_x_6073_, 0);
v_vs_6083_ = lean_ctor_get(v_x_6073_, 1);
v___x_6084_ = lean_unsigned_to_nat(0u);
v___x_6085_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6072_, v_ks_6082_, v_vs_6083_, v___x_6084_, v_x_6074_);
return v___x_6085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v_f_6086_, lean_object* v_x_6087_, lean_object* v_x_6088_){
_start:
{
lean_object* v_res_6089_; 
v_res_6089_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6086_, v_x_6087_, v_x_6088_);
lean_dec_ref(v_x_6087_);
return v_res_6089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_f_6090_, lean_object* v_as_6091_, lean_object* v_i_6092_, lean_object* v_stop_6093_, lean_object* v_b_6094_){
_start:
{
size_t v_i_boxed_6095_; size_t v_stop_boxed_6096_; lean_object* v_res_6097_; 
v_i_boxed_6095_ = lean_unbox_usize(v_i_6092_);
lean_dec(v_i_6092_);
v_stop_boxed_6096_ = lean_unbox_usize(v_stop_6093_);
lean_dec(v_stop_6093_);
v_res_6097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6090_, v_as_6091_, v_i_boxed_6095_, v_stop_boxed_6096_, v_b_6094_);
lean_dec_ref(v_as_6091_);
return v_res_6097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(lean_object* v_map_6098_, lean_object* v_f_6099_, lean_object* v_init_6100_){
_start:
{
lean_object* v___f_6101_; lean_object* v___x_6102_; 
v___f_6101_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_6101_, 0, v_f_6099_);
v___x_6102_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v___f_6101_, v_map_6098_, v_init_6100_);
return v___x_6102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_map_6103_, lean_object* v_f_6104_, lean_object* v_init_6105_){
_start:
{
lean_object* v_res_6106_; 
v_res_6106_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_6103_, v_f_6104_, v_init_6105_);
lean_dec_ref(v_map_6103_);
return v_res_6106_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(lean_object* v_f_6107_, lean_object* v_init_6108_, lean_object* v_m_6109_){
_start:
{
lean_object* v_map_u2081_6110_; lean_object* v_map_u2082_6111_; lean_object* v_buckets_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; uint8_t v___x_6115_; 
v_map_u2081_6110_ = lean_ctor_get(v_m_6109_, 0);
v_map_u2082_6111_ = lean_ctor_get(v_m_6109_, 1);
v_buckets_6112_ = lean_ctor_get(v_map_u2081_6110_, 1);
v___x_6113_ = lean_unsigned_to_nat(0u);
v___x_6114_ = lean_array_get_size(v_buckets_6112_);
v___x_6115_ = lean_nat_dec_lt(v___x_6113_, v___x_6114_);
if (v___x_6115_ == 0)
{
lean_object* v___x_6116_; 
v___x_6116_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_u2082_6111_, v_f_6107_, v_init_6108_);
return v___x_6116_;
}
else
{
size_t v___x_6117_; size_t v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; 
v___x_6117_ = ((size_t)0ULL);
v___x_6118_ = lean_usize_of_nat(v___x_6114_);
lean_inc(v_f_6107_);
v___x_6119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6107_, v_buckets_6112_, v___x_6117_, v___x_6118_, v_init_6108_);
v___x_6120_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_u2082_6111_, v_f_6107_, v___x_6119_);
return v___x_6120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg___boxed(lean_object* v_f_6121_, lean_object* v_init_6122_, lean_object* v_m_6123_){
_start:
{
lean_object* v_res_6124_; 
v_res_6124_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v_f_6121_, v_init_6122_, v_m_6123_);
lean_dec_ref(v_m_6123_);
return v_res_6124_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(lean_object* v_m_6126_){
_start:
{
lean_object* v___f_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; 
v___f_6127_ = ((lean_object*)(l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0));
v___x_6128_ = lean_box(0);
v___x_6129_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v___f_6127_, v___x_6128_, v_m_6126_);
return v___x_6129_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___boxed(lean_object* v_m_6130_){
_start:
{
lean_object* v_res_6131_; 
v_res_6131_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v_m_6130_);
lean_dec_ref(v_m_6130_);
return v_res_6131_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(lean_object* v_a_6132_, lean_object* v_a_6133_){
_start:
{
if (lean_obj_tag(v_a_6132_) == 0)
{
lean_object* v___x_6134_; 
v___x_6134_ = l_List_reverse___redArg(v_a_6133_);
return v___x_6134_;
}
else
{
lean_object* v_head_6135_; lean_object* v_tail_6136_; lean_object* v___x_6138_; uint8_t v_isShared_6139_; uint8_t v_isSharedCheck_6146_; 
v_head_6135_ = lean_ctor_get(v_a_6132_, 0);
v_tail_6136_ = lean_ctor_get(v_a_6132_, 1);
v_isSharedCheck_6146_ = !lean_is_exclusive(v_a_6132_);
if (v_isSharedCheck_6146_ == 0)
{
v___x_6138_ = v_a_6132_;
v_isShared_6139_ = v_isSharedCheck_6146_;
goto v_resetjp_6137_;
}
else
{
lean_inc(v_tail_6136_);
lean_inc(v_head_6135_);
lean_dec(v_a_6132_);
v___x_6138_ = lean_box(0);
v_isShared_6139_ = v_isSharedCheck_6146_;
goto v_resetjp_6137_;
}
v_resetjp_6137_:
{
uint8_t v___x_6140_; 
v___x_6140_ = l_Lean_Name_isInternal(v_head_6135_);
if (v___x_6140_ == 0)
{
lean_object* v___x_6142_; 
if (v_isShared_6139_ == 0)
{
lean_ctor_set(v___x_6138_, 1, v_a_6133_);
v___x_6142_ = v___x_6138_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6144_; 
v_reuseFailAlloc_6144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6144_, 0, v_head_6135_);
lean_ctor_set(v_reuseFailAlloc_6144_, 1, v_a_6133_);
v___x_6142_ = v_reuseFailAlloc_6144_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
v_a_6132_ = v_tail_6136_;
v_a_6133_ = v___x_6142_;
goto _start;
}
}
else
{
lean_del_object(v___x_6138_);
lean_dec(v_head_6135_);
v_a_6132_ = v_tail_6136_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(lean_object* v_a_6147_, lean_object* v_a_6148_){
_start:
{
if (lean_obj_tag(v_a_6147_) == 0)
{
lean_object* v___x_6149_; 
v___x_6149_ = l_List_reverse___redArg(v_a_6148_);
return v___x_6149_;
}
else
{
lean_object* v_head_6150_; lean_object* v_tail_6151_; lean_object* v___x_6153_; uint8_t v_isShared_6154_; uint8_t v_isSharedCheck_6160_; 
v_head_6150_ = lean_ctor_get(v_a_6147_, 0);
v_tail_6151_ = lean_ctor_get(v_a_6147_, 1);
v_isSharedCheck_6160_ = !lean_is_exclusive(v_a_6147_);
if (v_isSharedCheck_6160_ == 0)
{
v___x_6153_ = v_a_6147_;
v_isShared_6154_ = v_isSharedCheck_6160_;
goto v_resetjp_6152_;
}
else
{
lean_inc(v_tail_6151_);
lean_inc(v_head_6150_);
lean_dec(v_a_6147_);
v___x_6153_ = lean_box(0);
v_isShared_6154_ = v_isSharedCheck_6160_;
goto v_resetjp_6152_;
}
v_resetjp_6152_:
{
lean_object* v_fst_6155_; lean_object* v___x_6157_; 
v_fst_6155_ = lean_ctor_get(v_head_6150_, 0);
lean_inc(v_fst_6155_);
lean_dec(v_head_6150_);
if (v_isShared_6154_ == 0)
{
lean_ctor_set(v___x_6153_, 1, v_a_6148_);
lean_ctor_set(v___x_6153_, 0, v_fst_6155_);
v___x_6157_ = v___x_6153_;
goto v_reusejp_6156_;
}
else
{
lean_object* v_reuseFailAlloc_6159_; 
v_reuseFailAlloc_6159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6159_, 0, v_fst_6155_);
lean_ctor_set(v_reuseFailAlloc_6159_, 1, v_a_6148_);
v___x_6157_ = v_reuseFailAlloc_6159_;
goto v_reusejp_6156_;
}
v_reusejp_6156_:
{
v_a_6147_ = v_tail_6151_;
v_a_6148_ = v___x_6157_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv(lean_object* v_env_6161_, lean_object* v_constants_x3f_6162_, lean_object* v_cliOptions_6163_){
_start:
{
lean_object* v___y_6166_; 
if (lean_obj_tag(v_constants_x3f_6162_) == 0)
{
lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
lean_inc_ref(v_env_6161_);
v___x_6169_ = l_Lean_Environment_constants(v_env_6161_);
v___x_6170_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v___x_6169_);
lean_dec_ref(v___x_6169_);
v___x_6171_ = lean_box(0);
v___x_6172_ = l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(v___x_6170_, v___x_6171_);
v___x_6173_ = l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(v___x_6172_, v___x_6171_);
v___y_6166_ = v___x_6173_;
goto v___jp_6165_;
}
else
{
lean_object* v_val_6174_; 
v_val_6174_ = lean_ctor_get(v_constants_x3f_6162_, 0);
lean_inc(v_val_6174_);
lean_dec_ref_known(v_constants_x3f_6162_, 1);
v___y_6166_ = v_val_6174_;
goto v___jp_6165_;
}
v___jp_6165_:
{
lean_object* v___f_6167_; lean_object* v___x_6168_; 
lean_inc_ref(v_env_6161_);
v___f_6167_ = lean_alloc_closure((void*)(l_LeanExport_dumpEnv___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6167_, 0, v_env_6161_);
lean_closure_set(v___f_6167_, 1, v_cliOptions_6163_);
lean_closure_set(v___f_6167_, 2, v___y_6166_);
v___x_6168_ = l_LeanExport_M_run___redArg(v_env_6161_, v___f_6167_);
return v___x_6168_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___boxed(lean_object* v_env_6175_, lean_object* v_constants_x3f_6176_, lean_object* v_cliOptions_6177_, lean_object* v_a_6178_){
_start:
{
lean_object* v_res_6179_; 
v_res_6179_ = l_LeanExport_dumpEnv(v_env_6175_, v_constants_x3f_6176_, v_cliOptions_6177_);
return v_res_6179_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(lean_object* v_as_6180_, lean_object* v_as_x27_6181_, lean_object* v_b_6182_, lean_object* v_a_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_){
_start:
{
lean_object* v___x_6187_; 
v___x_6187_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_6181_, v_b_6182_, v___y_6184_, v___y_6185_);
return v___x_6187_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___boxed(lean_object* v_as_6188_, lean_object* v_as_x27_6189_, lean_object* v_b_6190_, lean_object* v_a_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_){
_start:
{
lean_object* v_res_6195_; 
v_res_6195_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(v_as_6188_, v_as_x27_6189_, v_b_6190_, v_a_6191_, v___y_6192_, v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec(v_as_x27_6189_);
lean_dec(v_as_6188_);
return v_res_6195_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(lean_object* v_00_u03b2_6196_, lean_object* v_m_6197_){
_start:
{
lean_object* v___x_6198_; 
v___x_6198_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v_m_6197_);
return v___x_6198_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___boxed(lean_object* v_00_u03b2_6199_, lean_object* v_m_6200_){
_start:
{
lean_object* v_res_6201_; 
v_res_6201_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(v_00_u03b2_6199_, v_m_6200_);
lean_dec_ref(v_m_6200_);
return v_res_6201_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(lean_object* v_00_u03b2_6202_, lean_object* v_00_u03c3_6203_, lean_object* v_f_6204_, lean_object* v_init_6205_, lean_object* v_m_6206_){
_start:
{
lean_object* v___x_6207_; 
v___x_6207_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v_f_6204_, v_init_6205_, v_m_6206_);
return v___x_6207_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___boxed(lean_object* v_00_u03b2_6208_, lean_object* v_00_u03c3_6209_, lean_object* v_f_6210_, lean_object* v_init_6211_, lean_object* v_m_6212_){
_start:
{
lean_object* v_res_6213_; 
v_res_6213_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(v_00_u03b2_6208_, v_00_u03c3_6209_, v_f_6210_, v_init_6211_, v_m_6212_);
lean_dec_ref(v_m_6212_);
return v_res_6213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_6214_, lean_object* v_00_u03c3_6215_, lean_object* v_f_6216_, lean_object* v_x_6217_, lean_object* v_x_6218_){
_start:
{
lean_object* v___x_6219_; 
v___x_6219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(v_f_6216_, v_x_6217_, v_x_6218_);
return v___x_6219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(lean_object* v_00_u03c3_6220_, lean_object* v_00_u03b2_6221_, lean_object* v_map_6222_, lean_object* v_f_6223_, lean_object* v_init_6224_){
_start:
{
lean_object* v___x_6225_; 
v___x_6225_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_6222_, v_f_6223_, v_init_6224_);
return v___x_6225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03c3_6226_, lean_object* v_00_u03b2_6227_, lean_object* v_map_6228_, lean_object* v_f_6229_, lean_object* v_init_6230_){
_start:
{
lean_object* v_res_6231_; 
v_res_6231_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(v_00_u03c3_6226_, v_00_u03b2_6227_, v_map_6228_, v_f_6229_, v_init_6230_);
lean_dec_ref(v_map_6228_);
return v_res_6231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_6232_, lean_object* v_00_u03c3_6233_, lean_object* v_f_6234_, lean_object* v_as_6235_, size_t v_i_6236_, size_t v_stop_6237_, lean_object* v_b_6238_){
_start:
{
lean_object* v___x_6239_; 
v___x_6239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6234_, v_as_6235_, v_i_6236_, v_stop_6237_, v_b_6238_);
return v___x_6239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_6240_, lean_object* v_00_u03c3_6241_, lean_object* v_f_6242_, lean_object* v_as_6243_, lean_object* v_i_6244_, lean_object* v_stop_6245_, lean_object* v_b_6246_){
_start:
{
size_t v_i_boxed_6247_; size_t v_stop_boxed_6248_; lean_object* v_res_6249_; 
v_i_boxed_6247_ = lean_unbox_usize(v_i_6244_);
lean_dec(v_i_6244_);
v_stop_boxed_6248_ = lean_unbox_usize(v_stop_6245_);
lean_dec(v_stop_6245_);
v_res_6249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(v_00_u03b2_6240_, v_00_u03c3_6241_, v_f_6242_, v_as_6243_, v_i_boxed_6247_, v_stop_boxed_6248_, v_b_6246_);
lean_dec_ref(v_as_6243_);
return v_res_6249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_map_6250_, lean_object* v_f_6251_, lean_object* v_init_6252_){
_start:
{
lean_object* v___x_6253_; 
v___x_6253_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6251_, v_map_6250_, v_init_6252_);
return v___x_6253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_map_6254_, lean_object* v_f_6255_, lean_object* v_init_6256_){
_start:
{
lean_object* v_res_6257_; 
v_res_6257_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(v_map_6254_, v_f_6255_, v_init_6256_);
lean_dec_ref(v_map_6254_);
return v_res_6257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_6258_, lean_object* v_00_u03b2_6259_, lean_object* v_map_6260_, lean_object* v_f_6261_, lean_object* v_init_6262_){
_start:
{
lean_object* v___x_6263_; 
v___x_6263_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6261_, v_map_6260_, v_init_6262_);
return v___x_6263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_6264_, lean_object* v_00_u03b2_6265_, lean_object* v_map_6266_, lean_object* v_f_6267_, lean_object* v_init_6268_){
_start:
{
lean_object* v_res_6269_; 
v_res_6269_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(v_00_u03c3_6264_, v_00_u03b2_6265_, v_map_6266_, v_f_6267_, v_init_6268_);
lean_dec_ref(v_map_6266_);
return v_res_6269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03c3_6270_, lean_object* v_00_u03b1_6271_, lean_object* v_00_u03b2_6272_, lean_object* v_f_6273_, lean_object* v_x_6274_, lean_object* v_x_6275_){
_start:
{
lean_object* v___x_6276_; 
v___x_6276_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6273_, v_x_6274_, v_x_6275_);
return v___x_6276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___boxed(lean_object* v_00_u03c3_6277_, lean_object* v_00_u03b1_6278_, lean_object* v_00_u03b2_6279_, lean_object* v_f_6280_, lean_object* v_x_6281_, lean_object* v_x_6282_){
_start:
{
lean_object* v_res_6283_; 
v_res_6283_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(v_00_u03c3_6277_, v_00_u03b1_6278_, v_00_u03b2_6279_, v_f_6280_, v_x_6281_, v_x_6282_);
lean_dec_ref(v_x_6281_);
return v_res_6283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_6284_, lean_object* v_00_u03b2_6285_, lean_object* v_00_u03c3_6286_, lean_object* v_f_6287_, lean_object* v_as_6288_, size_t v_i_6289_, size_t v_stop_6290_, lean_object* v_b_6291_){
_start:
{
lean_object* v___x_6292_; 
v___x_6292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6287_, v_as_6288_, v_i_6289_, v_stop_6290_, v_b_6291_);
return v___x_6292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_6293_, lean_object* v_00_u03b2_6294_, lean_object* v_00_u03c3_6295_, lean_object* v_f_6296_, lean_object* v_as_6297_, lean_object* v_i_6298_, lean_object* v_stop_6299_, lean_object* v_b_6300_){
_start:
{
size_t v_i_boxed_6301_; size_t v_stop_boxed_6302_; lean_object* v_res_6303_; 
v_i_boxed_6301_ = lean_unbox_usize(v_i_6298_);
lean_dec(v_i_6298_);
v_stop_boxed_6302_ = lean_unbox_usize(v_stop_6299_);
lean_dec(v_stop_6299_);
v_res_6303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(v_00_u03b1_6293_, v_00_u03b2_6294_, v_00_u03c3_6295_, v_f_6296_, v_as_6297_, v_i_boxed_6301_, v_stop_boxed_6302_, v_b_6300_);
lean_dec_ref(v_as_6297_);
return v_res_6303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(lean_object* v_00_u03c3_6304_, lean_object* v_00_u03b1_6305_, lean_object* v_00_u03b2_6306_, lean_object* v_f_6307_, lean_object* v_keys_6308_, lean_object* v_vals_6309_, lean_object* v_heq_6310_, lean_object* v_i_6311_, lean_object* v_acc_6312_){
_start:
{
lean_object* v___x_6313_; 
v___x_6313_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6307_, v_keys_6308_, v_vals_6309_, v_i_6311_, v_acc_6312_);
return v___x_6313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___boxed(lean_object* v_00_u03c3_6314_, lean_object* v_00_u03b1_6315_, lean_object* v_00_u03b2_6316_, lean_object* v_f_6317_, lean_object* v_keys_6318_, lean_object* v_vals_6319_, lean_object* v_heq_6320_, lean_object* v_i_6321_, lean_object* v_acc_6322_){
_start:
{
lean_object* v_res_6323_; 
v_res_6323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(v_00_u03c3_6314_, v_00_u03b1_6315_, v_00_u03b2_6316_, v_f_6317_, v_keys_6318_, v_vals_6319_, v_heq_6320_, v_i_6321_, v_acc_6322_);
lean_dec_ref(v_vals_6319_);
lean_dec_ref(v_keys_6318_);
return v_res_6323_;
}
}
lean_object* runtime_initialize_Lean(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_LeanExport_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_LeanExport_Basic_0__LeanExport_exportMetadata = _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata();
lean_mark_persistent(l___private_LeanExport_Basic_0__LeanExport_exportMetadata);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_LeanExport_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanExport_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_LeanExport_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_LeanExport_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_LeanExport_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
