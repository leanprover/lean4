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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Array_instInhabited(lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "--export-unsafe"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__1___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__1___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object*);
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
static lean_once_cell_t l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "LeanExport.dumpConstant"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 131, .m_data = "assertion violation: ((!recVal.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.2114.0 ).exportUnsafe)\n        "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__1_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "expected a `constantinfo.recinfo`."};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__3_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__6_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__7_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 135, .m_capacity = 135, .m_length = 134, .m_data = "assertion violation: ((!ctorVal.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.1873.0 ).exportUnsafe)\n          "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Expected a `ConstantInfo.ctorInfo`."};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0_value;
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "levelParams"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numParams"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numIndices"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ctors"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numNested"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isRec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "isReflexive"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isUnsafe"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "induct"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cidx"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numFields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nfields"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numMotives"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numMinors"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rules"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20(size_t, size_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value)}};
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
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object* v_x_626_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
uint8_t v___x_627_; 
v___x_627_ = 0;
return v___x_627_;
}
else
{
lean_object* v_head_628_; lean_object* v_tail_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_head_628_ = lean_ctor_get(v_x_626_, 0);
v_tail_629_ = lean_ctor_get(v_x_626_, 1);
v___x_630_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__1___closed__0));
v___x_631_ = lean_string_dec_eq(v_head_628_, v___x_630_);
if (v___x_631_ == 0)
{
v_x_626_ = v_tail_629_;
goto _start;
}
else
{
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object* v_x_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l_List_any___at___00LeanExport_initState_spec__1(v_x_633_);
lean_dec(v_x_633_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(lean_object* v_f_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
if (lean_obj_tag(v_x_638_) == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec_ref(v_f_636_);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v_x_637_);
lean_ctor_set(v___x_643_, 1, v___y_639_);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___y_641_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v_key_647_; lean_object* v_value_648_; lean_object* v_tail_649_; lean_object* v___x_650_; 
v_key_647_ = lean_ctor_get(v_x_638_, 0);
lean_inc(v_key_647_);
v_value_648_ = lean_ctor_get(v_x_638_, 1);
lean_inc(v_value_648_);
v_tail_649_ = lean_ctor_get(v_x_638_, 2);
lean_inc(v_tail_649_);
lean_dec_ref_known(v_x_638_, 3);
lean_inc_ref(v_f_636_);
lean_inc_ref(v___y_640_);
v___x_650_ = lean_apply_6(v_f_636_, v_key_647_, v_value_648_, v___y_639_, v___y_640_, v___y_641_, lean_box(0));
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v_fst_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
v_fst_652_ = lean_ctor_get(v_a_651_, 0);
if (lean_obj_tag(v_fst_652_) == 0)
{
lean_dec(v_a_651_);
lean_dec(v_tail_649_);
lean_dec_ref(v_f_636_);
return v___x_650_;
}
else
{
lean_object* v_a_653_; lean_object* v_snd_654_; lean_object* v_fst_655_; lean_object* v_snd_656_; 
lean_dec_ref_known(v___x_650_, 1);
v_a_653_ = lean_ctor_get(v_fst_652_, 0);
lean_inc(v_a_653_);
v_snd_654_ = lean_ctor_get(v_a_651_, 1);
lean_inc(v_snd_654_);
lean_dec(v_a_651_);
v_fst_655_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_fst_655_);
v_snd_656_ = lean_ctor_get(v_a_653_, 1);
lean_inc(v_snd_656_);
lean_dec(v_a_653_);
v_x_637_ = v_fst_655_;
v_x_638_ = v_tail_649_;
v___y_639_ = v_snd_656_;
v___y_641_ = v_snd_654_;
goto _start;
}
}
else
{
lean_dec(v_tail_649_);
lean_dec_ref(v_f_636_);
return v___x_650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___boxed(lean_object* v_f_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_658_, v_x_659_, v_x_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(lean_object* v_f_666_, lean_object* v_as_667_, size_t v_i_668_, size_t v_stop_669_, lean_object* v_b_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_eq(v_i_668_, v_stop_669_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_array_uget_borrowed(v_as_667_, v_i_668_);
v___x_677_ = lean_box(0);
lean_inc(v___x_676_);
lean_inc_ref(v_f_666_);
v___x_678_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_666_, v___x_677_, v___x_676_, v___y_671_, v___y_672_, v___y_673_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v_fst_680_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
v_fst_680_ = lean_ctor_get(v_a_679_, 0);
if (lean_obj_tag(v_fst_680_) == 0)
{
lean_dec(v_a_679_);
lean_dec_ref(v_f_666_);
return v___x_678_;
}
else
{
lean_object* v_a_681_; lean_object* v_snd_682_; lean_object* v_fst_683_; lean_object* v_snd_684_; size_t v___x_685_; size_t v___x_686_; 
lean_dec_ref_known(v___x_678_, 1);
v_a_681_ = lean_ctor_get(v_fst_680_, 0);
lean_inc(v_a_681_);
v_snd_682_ = lean_ctor_get(v_a_679_, 1);
lean_inc(v_snd_682_);
lean_dec(v_a_679_);
v_fst_683_ = lean_ctor_get(v_a_681_, 0);
lean_inc(v_fst_683_);
v_snd_684_ = lean_ctor_get(v_a_681_, 1);
lean_inc(v_snd_684_);
lean_dec(v_a_681_);
v___x_685_ = ((size_t)1ULL);
v___x_686_ = lean_usize_add(v_i_668_, v___x_685_);
v_i_668_ = v___x_686_;
v_b_670_ = v_fst_683_;
v___y_671_ = v_snd_684_;
v___y_673_ = v_snd_682_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_666_);
return v___x_678_;
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec_ref(v_f_666_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_b_670_);
lean_ctor_set(v___x_688_, 1, v___y_671_);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___y_673_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg___boxed(lean_object* v_f_692_, lean_object* v_as_693_, lean_object* v_i_694_, lean_object* v_stop_695_, lean_object* v_b_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
size_t v_i_boxed_701_; size_t v_stop_boxed_702_; lean_object* v_res_703_; 
v_i_boxed_701_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_stop_boxed_702_ = lean_unbox_usize(v_stop_695_);
lean_dec(v_stop_695_);
v_res_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_692_, v_as_693_, v_i_boxed_701_, v_stop_boxed_702_, v_b_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_as_693_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(lean_object* v_f_704_, lean_object* v_x_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
lean_inc_ref(v___y_709_);
v___x_712_ = lean_apply_6(v_f_704_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, lean_box(0));
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_f_713_, lean_object* v_x_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(v_f_713_, v_x_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(lean_object* v_f_722_, lean_object* v_keys_723_, lean_object* v_vals_724_, lean_object* v_i_725_, lean_object* v_acc_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_array_get_size(v_keys_723_);
v___x_732_ = lean_nat_dec_lt(v_i_725_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec(v_i_725_);
lean_dec_ref(v_f_722_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_acc_726_);
lean_ctor_set(v___x_733_, 1, v___y_727_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v___y_729_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
else
{
lean_object* v_k_737_; lean_object* v_v_738_; lean_object* v___x_739_; 
v_k_737_ = lean_array_fget_borrowed(v_keys_723_, v_i_725_);
v_v_738_ = lean_array_fget_borrowed(v_vals_724_, v_i_725_);
lean_inc_ref(v_f_722_);
lean_inc_ref(v___y_728_);
lean_inc(v_v_738_);
lean_inc(v_k_737_);
v___x_739_ = lean_apply_7(v_f_722_, v_acc_726_, v_k_737_, v_v_738_, v___y_727_, v___y_728_, v___y_729_, lean_box(0));
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v_fst_741_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
v_fst_741_ = lean_ctor_get(v_a_740_, 0);
if (lean_obj_tag(v_fst_741_) == 0)
{
lean_dec(v_a_740_);
lean_dec(v_i_725_);
lean_dec_ref(v_f_722_);
return v___x_739_;
}
else
{
lean_object* v_a_742_; lean_object* v_snd_743_; lean_object* v_fst_744_; lean_object* v_snd_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec_ref_known(v___x_739_, 1);
v_a_742_ = lean_ctor_get(v_fst_741_, 0);
lean_inc(v_a_742_);
v_snd_743_ = lean_ctor_get(v_a_740_, 1);
lean_inc(v_snd_743_);
lean_dec(v_a_740_);
v_fst_744_ = lean_ctor_get(v_a_742_, 0);
lean_inc(v_fst_744_);
v_snd_745_ = lean_ctor_get(v_a_742_, 1);
lean_inc(v_snd_745_);
lean_dec(v_a_742_);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_i_725_, v___x_746_);
lean_dec(v_i_725_);
v_i_725_ = v___x_747_;
v_acc_726_ = v_fst_744_;
v___y_727_ = v_snd_745_;
v___y_729_ = v_snd_743_;
goto _start;
}
}
else
{
lean_dec(v_i_725_);
lean_dec_ref(v_f_722_);
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_f_749_, lean_object* v_keys_750_, lean_object* v_vals_751_, lean_object* v_i_752_, lean_object* v_acc_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_749_, v_keys_750_, v_vals_751_, v_i_752_, v_acc_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec_ref(v_vals_751_);
lean_dec_ref(v_keys_750_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_f_759_, lean_object* v_as_760_, size_t v_i_761_, size_t v_stop_762_, lean_object* v_b_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_fst_769_; lean_object* v_snd_770_; lean_object* v_snd_771_; lean_object* v___y_776_; uint8_t v___x_783_; 
v___x_783_ = lean_usize_dec_eq(v_i_761_, v_stop_762_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
v___x_784_ = lean_array_uget_borrowed(v_as_760_, v_i_761_);
switch(lean_obj_tag(v___x_784_))
{
case 0:
{
lean_object* v_key_785_; lean_object* v_val_786_; lean_object* v___x_787_; 
v_key_785_ = lean_ctor_get(v___x_784_, 0);
v_val_786_ = lean_ctor_get(v___x_784_, 1);
lean_inc_ref(v_f_759_);
lean_inc_ref(v___y_765_);
lean_inc(v_val_786_);
lean_inc(v_key_785_);
v___x_787_ = lean_apply_7(v_f_759_, v_b_763_, v_key_785_, v_val_786_, v___y_764_, v___y_765_, v___y_766_, lean_box(0));
v___y_776_ = v___x_787_;
goto v___jp_775_;
}
case 1:
{
lean_object* v_node_788_; lean_object* v___x_789_; 
v_node_788_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_node_788_);
lean_inc_ref(v_f_759_);
v___x_789_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_759_, v_node_788_, v_b_763_, v___y_764_, v___y_765_, v___y_766_);
v___y_776_ = v___x_789_;
goto v___jp_775_;
}
default: 
{
v_fst_769_ = v_b_763_;
v_snd_770_ = v___y_764_;
v_snd_771_ = v___y_766_;
goto v___jp_768_;
}
}
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v_f_759_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_b_763_);
lean_ctor_set(v___x_790_, 1, v___y_764_);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___y_766_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
v___jp_768_:
{
size_t v___x_772_; size_t v___x_773_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_761_, v___x_772_);
v_i_761_ = v___x_773_;
v_b_763_ = v_fst_769_;
v___y_764_ = v_snd_770_;
v___y_766_ = v_snd_771_;
goto _start;
}
v___jp_775_:
{
if (lean_obj_tag(v___y_776_) == 0)
{
lean_object* v_a_777_; lean_object* v_fst_778_; 
v_a_777_ = lean_ctor_get(v___y_776_, 0);
v_fst_778_ = lean_ctor_get(v_a_777_, 0);
if (lean_obj_tag(v_fst_778_) == 0)
{
lean_dec_ref(v_f_759_);
return v___y_776_;
}
else
{
lean_object* v_a_779_; lean_object* v_snd_780_; lean_object* v_fst_781_; lean_object* v_snd_782_; 
lean_inc(v_a_777_);
lean_dec_ref_known(v___y_776_, 1);
v_a_779_ = lean_ctor_get(v_fst_778_, 0);
lean_inc(v_a_779_);
v_snd_780_ = lean_ctor_get(v_a_777_, 1);
lean_inc(v_snd_780_);
lean_dec(v_a_777_);
v_fst_781_ = lean_ctor_get(v_a_779_, 0);
lean_inc(v_fst_781_);
v_snd_782_ = lean_ctor_get(v_a_779_, 1);
lean_inc(v_snd_782_);
lean_dec(v_a_779_);
v_fst_769_ = v_fst_781_;
v_snd_770_ = v_snd_782_;
v_snd_771_ = v_snd_780_;
goto v___jp_768_;
}
}
else
{
lean_dec_ref(v_f_759_);
return v___y_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_f_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
if (lean_obj_tag(v_x_795_) == 0)
{
lean_object* v_es_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_817_; 
v_es_801_ = lean_ctor_get(v_x_795_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_795_);
if (v_isSharedCheck_817_ == 0)
{
v___x_803_ = v_x_795_;
v_isShared_804_ = v_isSharedCheck_817_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_es_801_);
lean_dec(v_x_795_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_817_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_array_get_size(v_es_801_);
v___x_807_ = lean_nat_dec_lt(v___x_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec_ref(v_es_801_);
lean_dec_ref(v_f_794_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_x_796_);
lean_ctor_set(v___x_808_, 1, v___y_797_);
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 1);
lean_ctor_set(v___x_803_, 0, v___x_808_);
v___x_810_ = v___x_803_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_813_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___y_799_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
else
{
size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; 
lean_del_object(v___x_803_);
v___x_814_ = ((size_t)0ULL);
v___x_815_ = lean_usize_of_nat(v___x_806_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_794_, v_es_801_, v___x_814_, v___x_815_, v_x_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec_ref(v_es_801_);
return v___x_816_;
}
}
}
else
{
lean_object* v_ks_818_; lean_object* v_vs_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_ks_818_ = lean_ctor_get(v_x_795_, 0);
lean_inc_ref(v_ks_818_);
v_vs_819_ = lean_ctor_get(v_x_795_, 1);
lean_inc_ref(v_vs_819_);
lean_dec_ref_known(v_x_795_, 2);
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_794_, v_ks_818_, v_vs_819_, v___x_820_, v_x_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec_ref(v_vs_819_);
lean_dec_ref(v_ks_818_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_f_822_, lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_822_, v_x_823_, v_x_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec_ref(v___y_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_f_830_, lean_object* v_as_831_, lean_object* v_i_832_, lean_object* v_stop_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
size_t v_i_boxed_839_; size_t v_stop_boxed_840_; lean_object* v_res_841_; 
v_i_boxed_839_ = lean_unbox_usize(v_i_832_);
lean_dec(v_i_832_);
v_stop_boxed_840_ = lean_unbox_usize(v_stop_833_);
lean_dec(v_stop_833_);
v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_830_, v_as_831_, v_i_boxed_839_, v_stop_boxed_840_, v_b_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v_as_831_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(lean_object* v_map_842_, lean_object* v_f_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___f_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___f_848_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_848_, 0, v_f_843_);
v___x_849_ = lean_box(0);
v___x_850_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v___f_848_, v_map_842_, v___x_849_, v___y_844_, v___y_845_, v___y_846_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___boxed(lean_object* v_map_851_, lean_object* v_f_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_851_, v_f_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(lean_object* v_s_858_, lean_object* v_f_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_map_u2081_864_; lean_object* v_map_u2082_865_; lean_object* v_buckets_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_map_u2081_864_ = lean_ctor_get(v_s_858_, 0);
lean_inc_ref(v_map_u2081_864_);
v_map_u2082_865_ = lean_ctor_get(v_s_858_, 1);
lean_inc_ref(v_map_u2082_865_);
lean_dec_ref(v_s_858_);
v_buckets_866_ = lean_ctor_get(v_map_u2081_864_, 1);
lean_inc_ref(v_buckets_866_);
lean_dec_ref(v_map_u2081_864_);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_array_get_size(v_buckets_866_);
v___x_869_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
lean_dec_ref(v_buckets_866_);
v___x_870_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_865_, v_f_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; size_t v___x_872_; size_t v___x_873_; lean_object* v___x_874_; 
v___x_871_ = lean_box(0);
v___x_872_ = ((size_t)0ULL);
v___x_873_ = lean_usize_of_nat(v___x_868_);
lean_inc_ref(v_f_859_);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_859_, v_buckets_866_, v___x_872_, v___x_873_, v___x_871_, v___y_860_, v___y_861_, v___y_862_);
lean_dec_ref(v_buckets_866_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v_fst_876_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
v_fst_876_ = lean_ctor_get(v_a_875_, 0);
if (lean_obj_tag(v_fst_876_) == 0)
{
lean_dec(v_a_875_);
lean_dec_ref(v_map_u2082_865_);
lean_dec_ref(v_f_859_);
return v___x_874_;
}
else
{
lean_object* v_a_877_; lean_object* v_snd_878_; lean_object* v_snd_879_; lean_object* v___x_880_; 
lean_dec_ref_known(v___x_874_, 1);
v_a_877_ = lean_ctor_get(v_fst_876_, 0);
lean_inc(v_a_877_);
v_snd_878_ = lean_ctor_get(v_a_875_, 1);
lean_inc(v_snd_878_);
lean_dec(v_a_875_);
v_snd_879_ = lean_ctor_get(v_a_877_, 1);
lean_inc(v_snd_879_);
lean_dec(v_a_877_);
v___x_880_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_865_, v_f_859_, v_snd_879_, v___y_861_, v_snd_878_);
return v___x_880_;
}
}
else
{
lean_dec_ref(v_map_u2082_865_);
lean_dec_ref(v_f_859_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg___boxed(lean_object* v_s_881_, lean_object* v_f_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_881_, v_f_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState(lean_object* v_env_889_, lean_object* v_cliOptions_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___f_894_; lean_object* v_recursorMap_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___f_894_ = ((lean_object*)(l_LeanExport_initState___closed__0));
v_recursorMap_895_ = lean_box(1);
v___x_896_ = l_Lean_Environment_constants(v_env_889_);
v___x_897_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v___x_896_, v___f_894_, v_recursorMap_895_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_936_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_936_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_936_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_936_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_fst_902_; lean_object* v_snd_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_935_; 
v_fst_902_ = lean_ctor_get(v_a_898_, 0);
v_snd_903_ = lean_ctor_get(v_a_898_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_a_898_);
if (v_isSharedCheck_935_ == 0)
{
v___x_905_ = v_a_898_;
v_isShared_906_ = v_isSharedCheck_935_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_snd_903_);
lean_inc(v_fst_902_);
lean_dec(v_a_898_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_935_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_fst_908_; 
if (lean_obj_tag(v_fst_902_) == 0)
{
lean_object* v_a_932_; 
v_a_932_ = lean_ctor_get(v_fst_902_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v_fst_902_, 1);
v_fst_908_ = v_a_932_;
goto v___jp_907_;
}
else
{
lean_object* v_a_933_; lean_object* v_snd_934_; 
v_a_933_ = lean_ctor_get(v_fst_902_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v_fst_902_, 1);
v_snd_934_ = lean_ctor_get(v_a_933_, 1);
lean_inc(v_snd_934_);
lean_dec(v_a_933_);
v_fst_908_ = v_snd_934_;
goto v___jp_907_;
}
v___jp_907_:
{
lean_object* v_visitedNames_909_; lean_object* v_visitedLevels_910_; lean_object* v_visitedExprs_911_; lean_object* v_visitedConstants_912_; lean_object* v_noMDataExprs_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_930_; 
v_visitedNames_909_ = lean_ctor_get(v_snd_903_, 0);
v_visitedLevels_910_ = lean_ctor_get(v_snd_903_, 1);
v_visitedExprs_911_ = lean_ctor_get(v_snd_903_, 2);
v_visitedConstants_912_ = lean_ctor_get(v_snd_903_, 3);
v_noMDataExprs_913_ = lean_ctor_get(v_snd_903_, 4);
v_isSharedCheck_930_ = !lean_is_exclusive(v_snd_903_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_snd_903_, 5);
lean_dec(v_unused_931_);
v___x_915_ = v_snd_903_;
v_isShared_916_ = v_isSharedCheck_930_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_noMDataExprs_913_);
lean_inc(v_visitedConstants_912_);
lean_inc(v_visitedExprs_911_);
lean_inc(v_visitedLevels_910_);
lean_inc(v_visitedNames_909_);
lean_dec(v_snd_903_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_930_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; uint8_t v___x_918_; uint8_t v___x_919_; uint8_t v___x_920_; lean_object* v___x_922_; 
v___x_917_ = lean_box(0);
v___x_918_ = l_List_any___at___00LeanExport_initState_spec__0(v_cliOptions_890_);
v___x_919_ = l_List_any___at___00LeanExport_initState_spec__1(v_cliOptions_890_);
v___x_920_ = l_List_any___at___00LeanExport_initState_spec__2(v_cliOptions_890_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 5, v_fst_908_);
v___x_922_ = v___x_915_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_visitedNames_909_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_visitedLevels_910_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_visitedExprs_911_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_visitedConstants_912_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v_noMDataExprs_913_);
lean_ctor_set(v_reuseFailAlloc_929_, 5, v_fst_908_);
v___x_922_ = v_reuseFailAlloc_929_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*6, v___x_918_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*6 + 1, v___x_919_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*6 + 2, v___x_920_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v___x_922_);
lean_ctor_set(v___x_905_, 0, v___x_917_);
v___x_924_ = v___x_905_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___x_922_);
v___x_924_ = v_reuseFailAlloc_928_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_924_);
v___x_926_ = v___x_900_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
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
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_a_937_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_897_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_897_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___boxed(lean_object* v_env_945_, lean_object* v_cliOptions_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_LeanExport_initState(v_env_945_, v_cliOptions_946_, v_a_947_, v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_cliOptions_946_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3(lean_object* v_val_951_, lean_object* v_k_952_, lean_object* v_t_953_, lean_object* v_hl_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_951_, v_k_952_, v_t_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(lean_object* v_val_956_, lean_object* v_as_957_, lean_object* v_as_x27_958_, lean_object* v_b_959_, lean_object* v_a_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_956_, v_as_x27_958_, v_b_959_, v___y_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___boxed(lean_object* v_val_965_, lean_object* v_as_966_, lean_object* v_as_x27_967_, lean_object* v_b_968_, lean_object* v_a_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(v_val_965_, v_as_966_, v_as_x27_967_, v_b_968_, v_a_969_, v___y_970_, v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v_as_x27_967_);
lean_dec(v_as_966_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(lean_object* v_00_u03b2_974_, lean_object* v_s_975_, lean_object* v_f_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_975_, v_f_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___boxed(lean_object* v_00_u03b2_982_, lean_object* v_s_983_, lean_object* v_f_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(v_00_u03b2_982_, v_s_983_, v_f_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_object* v_00_u03b2_990_, lean_object* v_f_991_, lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_991_, v_x_992_, v_x_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___boxed(lean_object* v_00_u03b2_999_, lean_object* v_f_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(v_00_u03b2_999_, v_f_1000_, v_x_1001_, v_x_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_object* v_00_u03b2_1008_, lean_object* v_map_1009_, lean_object* v_f_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_1009_, v_f_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1016_, lean_object* v_map_1017_, lean_object* v_f_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(v_00_u03b2_1016_, v_map_1017_, v_f_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(lean_object* v_00_u03b2_1024_, lean_object* v_f_1025_, lean_object* v_as_1026_, size_t v_i_1027_, size_t v_stop_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_1025_, v_as_1026_, v_i_1027_, v_stop_1028_, v_b_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1035_, lean_object* v_f_1036_, lean_object* v_as_1037_, lean_object* v_i_1038_, lean_object* v_stop_1039_, lean_object* v_b_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
size_t v_i_boxed_1045_; size_t v_stop_boxed_1046_; lean_object* v_res_1047_; 
v_i_boxed_1045_ = lean_unbox_usize(v_i_1038_);
lean_dec(v_i_1038_);
v_stop_boxed_1046_ = lean_unbox_usize(v_stop_1039_);
lean_dec(v_stop_1039_);
v_res_1047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(v_00_u03b2_1035_, v_f_1036_, v_as_1037_, v_i_boxed_1045_, v_stop_boxed_1046_, v_b_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec_ref(v_as_1037_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(lean_object* v_map_1048_, lean_object* v_f_1049_, lean_object* v_init_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1049_, v_map_1048_, v_init_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_map_1056_, lean_object* v_f_1057_, lean_object* v_init_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(v_map_1056_, v_f_1057_, v_init_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(lean_object* v_00_u03c3_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_map_1066_, lean_object* v_f_1067_, lean_object* v_init_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1067_, v_map_1066_, v_init_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03c3_1074_, lean_object* v_00_u03b2_1075_, lean_object* v_map_1076_, lean_object* v_f_1077_, lean_object* v_init_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(v_00_u03c3_1074_, v_00_u03b2_1075_, v_map_1076_, v_f_1077_, v_init_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec_ref(v___y_1080_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03c3_1084_, lean_object* v_00_u03b1_1085_, lean_object* v_00_u03b2_1086_, lean_object* v_f_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1087_, v_x_1088_, v_x_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03c3_1095_, lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_f_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(v_00_u03c3_1095_, v_00_u03b1_1096_, v_00_u03b2_1097_, v_f_1098_, v_x_1099_, v_x_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_00_u03c3_1108_, lean_object* v_f_1109_, lean_object* v_as_1110_, size_t v_i_1111_, size_t v_stop_1112_, lean_object* v_b_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_1109_, v_as_1110_, v_i_1111_, v_stop_1112_, v_b_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_00_u03c3_1121_, lean_object* v_f_1122_, lean_object* v_as_1123_, lean_object* v_i_1124_, lean_object* v_stop_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
size_t v_i_boxed_1131_; size_t v_stop_boxed_1132_; lean_object* v_res_1133_; 
v_i_boxed_1131_ = lean_unbox_usize(v_i_1124_);
lean_dec(v_i_1124_);
v_stop_boxed_1132_ = lean_unbox_usize(v_stop_1125_);
lean_dec(v_stop_1125_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_1119_, v_00_u03b2_1120_, v_00_u03c3_1121_, v_f_1122_, v_as_1123_, v_i_boxed_1131_, v_stop_boxed_1132_, v_b_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_as_1123_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(lean_object* v_00_u03c3_1134_, lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_f_1137_, lean_object* v_keys_1138_, lean_object* v_vals_1139_, lean_object* v_heq_1140_, lean_object* v_i_1141_, lean_object* v_acc_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_1137_, v_keys_1138_, v_vals_1139_, v_i_1141_, v_acc_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03c3_1148_, lean_object* v_00_u03b1_1149_, lean_object* v_00_u03b2_1150_, lean_object* v_f_1151_, lean_object* v_keys_1152_, lean_object* v_vals_1153_, lean_object* v_heq_1154_, lean_object* v_i_1155_, lean_object* v_acc_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(v_00_u03c3_1148_, v_00_u03b1_1149_, v_00_u03b2_1150_, v_f_1151_, v_keys_1152_, v_vals_1153_, v_heq_1154_, v_i_1155_, v_acc_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v_vals_1153_);
lean_dec_ref(v_keys_1152_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_x_1165_, lean_object* v_namespaced_1166_, lean_object* v_getM_1167_, lean_object* v_setM_1168_, lean_object* v_rec_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_inc_ref(v_getM_1167_);
lean_inc_ref(v_a_1171_);
v___x_1173_ = lean_apply_1(v_getM_1167_, v_a_1171_);
lean_inc(v_x_1165_);
lean_inc_ref(v_inst_1163_);
lean_inc_ref(v_inst_1164_);
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1164_, v_inst_1163_, v___x_1173_, v_x_1165_);
lean_dec_ref(v___x_1173_);
if (lean_obj_tag(v___x_1174_) == 1)
{
lean_object* v_val_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_rec_1169_);
lean_dec_ref(v_setM_1168_);
lean_dec_ref(v_getM_1167_);
lean_dec_ref(v_namespaced_1166_);
lean_dec(v_x_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec_ref(v_inst_1163_);
v_val_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_val_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_val_1175_);
lean_ctor_set(v___x_1179_, 1, v_a_1171_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
lean_object* v___x_1184_; 
lean_dec(v___x_1174_);
lean_inc_ref(v_a_1170_);
v___x_1184_ = lean_apply_3(v_rec_1169_, v_a_1170_, v_a_1171_, lean_box(0));
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v_fst_1186_; lean_object* v_snd_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1220_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v_fst_1186_ = lean_ctor_get(v_a_1185_, 0);
v_snd_1187_ = lean_ctor_get(v_a_1185_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_a_1185_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1189_ = v_a_1185_;
v_isShared_1190_ = v_isSharedCheck_1220_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_snd_1187_);
lean_inc(v_fst_1186_);
lean_dec(v_a_1185_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1220_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v_size_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_inc(v_snd_1187_);
v___x_1191_ = lean_apply_1(v_getM_1167_, v_snd_1187_);
v_size_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_n(v_size_1192_, 2);
v___f_1193_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
v___x_1194_ = l_Lean_JsonNumber_fromNat(v_size_1192_);
v___x_1195_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
v___x_1196_ = l_Lean_Json_setObjVal_x21(v_fst_1186_, v_namespaced_1166_, v___x_1195_);
v___x_1197_ = l_Lean_Json_compress(v___x_1196_);
v___x_1198_ = l_IO_println___redArg(v___f_1193_, v___x_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1210_; 
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v___x_1198_, 0);
lean_dec(v_unused_1211_);
v___x_1200_ = v___x_1198_;
v_isShared_1201_ = v_isSharedCheck_1210_;
goto v_resetjp_1199_;
}
else
{
lean_dec(v___x_1198_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1210_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
lean_inc(v_size_1192_);
v___x_1202_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1164_, v_inst_1163_, v___x_1191_, v_x_1165_, v_size_1192_);
v___x_1203_ = lean_apply_2(v_setM_1168_, v_snd_1187_, v___x_1202_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1203_);
lean_ctor_set(v___x_1189_, 0, v_size_1192_);
v___x_1205_ = v___x_1189_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_size_1192_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1205_);
v___x_1207_ = v___x_1200_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
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
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v_size_1192_);
lean_dec_ref(v___x_1191_);
lean_del_object(v___x_1189_);
lean_dec(v_snd_1187_);
lean_dec_ref(v_setM_1168_);
lean_dec(v_x_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec_ref(v_inst_1163_);
v_a_1212_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1198_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1198_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
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
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_setM_1168_);
lean_dec_ref(v_getM_1167_);
lean_dec_ref(v_namespaced_1166_);
lean_dec(v_x_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec_ref(v_inst_1163_);
v_a_1221_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1184_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1184_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
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
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___boxed(lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_x_1231_, lean_object* v_namespaced_1232_, lean_object* v_getM_1233_, lean_object* v_setM_1234_, lean_object* v_rec_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(v_inst_1229_, v_inst_1230_, v_x_1231_, v_namespaced_1232_, v_getM_1233_, v_setM_1234_, v_rec_1235_, v_a_1236_, v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx(lean_object* v_00_u03b1_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_x_1243_, lean_object* v_namespaced_1244_, lean_object* v_getM_1245_, lean_object* v_setM_1246_, lean_object* v_rec_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_inc_ref(v_getM_1245_);
lean_inc_ref(v_a_1249_);
v___x_1251_ = lean_apply_1(v_getM_1245_, v_a_1249_);
lean_inc(v_x_1243_);
lean_inc_ref(v_inst_1241_);
lean_inc_ref(v_inst_1242_);
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1242_, v_inst_1241_, v___x_1251_, v_x_1243_);
lean_dec_ref(v___x_1251_);
if (lean_obj_tag(v___x_1252_) == 1)
{
lean_object* v_val_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_rec_1247_);
lean_dec_ref(v_setM_1246_);
lean_dec_ref(v_getM_1245_);
lean_dec_ref(v_namespaced_1244_);
lean_dec(v_x_1243_);
lean_dec_ref(v_inst_1242_);
lean_dec_ref(v_inst_1241_);
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1261_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_val_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1261_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_val_1253_);
lean_ctor_set(v___x_1257_, 1, v_a_1249_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1257_);
v___x_1259_ = v___x_1255_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v___x_1262_; 
lean_dec(v___x_1252_);
lean_inc_ref(v_a_1248_);
v___x_1262_ = lean_apply_3(v_rec_1247_, v_a_1248_, v_a_1249_, lean_box(0));
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v_fst_1264_; lean_object* v_snd_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1298_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v_fst_1264_ = lean_ctor_get(v_a_1263_, 0);
v_snd_1265_ = lean_ctor_get(v_a_1263_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_a_1263_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1267_ = v_a_1263_;
v_isShared_1268_ = v_isSharedCheck_1298_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_snd_1265_);
lean_inc(v_fst_1264_);
lean_dec(v_a_1263_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1298_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v_size_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_inc(v_snd_1265_);
v___x_1269_ = lean_apply_1(v_getM_1245_, v_snd_1265_);
v_size_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc_n(v_size_1270_, 2);
v___f_1271_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
v___x_1272_ = l_Lean_JsonNumber_fromNat(v_size_1270_);
v___x_1273_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
v___x_1274_ = l_Lean_Json_setObjVal_x21(v_fst_1264_, v_namespaced_1244_, v___x_1273_);
v___x_1275_ = l_Lean_Json_compress(v___x_1274_);
v___x_1276_ = l_IO_println___redArg(v___f_1271_, v___x_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1288_; 
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v___x_1276_, 0);
lean_dec(v_unused_1289_);
v___x_1278_ = v___x_1276_;
v_isShared_1279_ = v_isSharedCheck_1288_;
goto v_resetjp_1277_;
}
else
{
lean_dec(v___x_1276_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1288_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_inc(v_size_1270_);
v___x_1280_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1242_, v_inst_1241_, v___x_1269_, v_x_1243_, v_size_1270_);
v___x_1281_ = lean_apply_2(v_setM_1246_, v_snd_1265_, v___x_1280_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v___x_1281_);
lean_ctor_set(v___x_1267_, 0, v_size_1270_);
v___x_1283_ = v___x_1267_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_size_1270_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1285_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1283_);
v___x_1285_ = v___x_1278_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
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
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_size_1270_);
lean_dec_ref(v___x_1269_);
lean_del_object(v___x_1267_);
lean_dec(v_snd_1265_);
lean_dec_ref(v_setM_1246_);
lean_dec(v_x_1243_);
lean_dec_ref(v_inst_1242_);
lean_dec_ref(v_inst_1241_);
v_a_1290_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1276_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1276_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v_setM_1246_);
lean_dec_ref(v_getM_1245_);
lean_dec_ref(v_namespaced_1244_);
lean_dec(v_x_1243_);
lean_dec_ref(v_inst_1242_);
lean_dec_ref(v_inst_1241_);
v_a_1299_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1262_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1262_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_x_1310_, lean_object* v_namespaced_1311_, lean_object* v_getM_1312_, lean_object* v_setM_1313_, lean_object* v_rec_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_LeanExport_Basic_0__LeanExport_getIdx(v_00_u03b1_1307_, v_inst_1308_, v_inst_1309_, v_x_1310_, v_namespaced_1311_, v_getM_1312_, v_setM_1313_, v_rec_1314_, v_a_1315_, v_a_1316_);
lean_dec_ref(v_a_1315_);
return v_res_1318_;
}
}
static lean_object* _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_instMonadEIO(lean_box(0));
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(lean_object* v_msg_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___f_1337_; lean_object* v___x_1421__overap_1338_; lean_object* v___x_1339_; 
v___x_1324_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_1325_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1325_, 0, v___x_1324_);
v___f_1326_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1326_, 0, v___x_1324_);
v___f_1327_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1327_, 0, v___x_1324_);
v___f_1328_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1328_, 0, v___x_1324_);
v___x_1329_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1329_, 0, lean_box(0));
lean_closure_set(v___x_1329_, 1, lean_box(0));
lean_closure_set(v___x_1329_, 2, v___x_1324_);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v___f_1325_);
v___x_1331_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1331_, 0, lean_box(0));
lean_closure_set(v___x_1331_, 1, lean_box(0));
lean_closure_set(v___x_1331_, 2, v___x_1324_);
v___x_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
lean_ctor_set(v___x_1332_, 2, v___f_1326_);
lean_ctor_set(v___x_1332_, 3, v___f_1327_);
lean_ctor_set(v___x_1332_, 4, v___f_1328_);
v___x_1333_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1333_, 0, lean_box(0));
lean_closure_set(v___x_1333_, 1, lean_box(0));
lean_closure_set(v___x_1333_, 2, v___x_1324_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = lean_box(0);
v___x_1336_ = l_instInhabitedOfMonad___redArg(v___x_1334_, v___x_1335_);
v___f_1337_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1337_, 0, v___x_1336_);
v___x_1421__overap_1338_ = lean_panic_fn_borrowed(v___f_1337_, v_msg_1320_);
lean_dec_ref(v___f_1337_);
lean_inc_ref(v___y_1321_);
v___x_1339_ = lean_apply_3(v___x_1421__overap_1338_, v___y_1321_, v___y_1322_, lean_box(0));
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___boxed(lean_object* v_msg_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v_msg_1340_, v___y_1341_, v___y_1342_);
lean_dec_ref(v___y_1341_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(lean_object* v_a_1345_, lean_object* v_x_1346_){
_start:
{
if (lean_obj_tag(v_x_1346_) == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_box(0);
return v___x_1347_;
}
else
{
lean_object* v_key_1348_; lean_object* v_value_1349_; lean_object* v_tail_1350_; uint8_t v___x_1351_; 
v_key_1348_ = lean_ctor_get(v_x_1346_, 0);
v_value_1349_ = lean_ctor_get(v_x_1346_, 1);
v_tail_1350_ = lean_ctor_get(v_x_1346_, 2);
v___x_1351_ = lean_name_eq(v_key_1348_, v_a_1345_);
if (v___x_1351_ == 0)
{
v_x_1346_ = v_tail_1350_;
goto _start;
}
else
{
lean_object* v___x_1353_; 
lean_inc(v_value_1349_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_value_1349_);
return v___x_1353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg___boxed(lean_object* v_a_1354_, lean_object* v_x_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1354_, v_x_1355_);
lean_dec(v_x_1355_);
lean_dec(v_a_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(lean_object* v_m_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_buckets_1359_; lean_object* v___x_1360_; uint64_t v___y_1362_; 
v_buckets_1359_ = lean_ctor_get(v_m_1357_, 1);
v___x_1360_ = lean_array_get_size(v_buckets_1359_);
if (lean_obj_tag(v_a_1358_) == 0)
{
uint64_t v___x_1376_; 
v___x_1376_ = 1723ULL;
v___y_1362_ = v___x_1376_;
goto v___jp_1361_;
}
else
{
uint64_t v_hash_1377_; 
v_hash_1377_ = lean_ctor_get_uint64(v_a_1358_, sizeof(void*)*2);
v___y_1362_ = v_hash_1377_;
goto v___jp_1361_;
}
v___jp_1361_:
{
uint64_t v___x_1363_; uint64_t v___x_1364_; uint64_t v_fold_1365_; uint64_t v___x_1366_; uint64_t v___x_1367_; uint64_t v___x_1368_; size_t v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1363_ = 32ULL;
v___x_1364_ = lean_uint64_shift_right(v___y_1362_, v___x_1363_);
v_fold_1365_ = lean_uint64_xor(v___y_1362_, v___x_1364_);
v___x_1366_ = 16ULL;
v___x_1367_ = lean_uint64_shift_right(v_fold_1365_, v___x_1366_);
v___x_1368_ = lean_uint64_xor(v_fold_1365_, v___x_1367_);
v___x_1369_ = lean_uint64_to_usize(v___x_1368_);
v___x_1370_ = lean_usize_of_nat(v___x_1360_);
v___x_1371_ = ((size_t)1ULL);
v___x_1372_ = lean_usize_sub(v___x_1370_, v___x_1371_);
v___x_1373_ = lean_usize_land(v___x_1369_, v___x_1372_);
v___x_1374_ = lean_array_uget_borrowed(v_buckets_1359_, v___x_1373_);
v___x_1375_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1358_, v___x_1374_);
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg___boxed(lean_object* v_m_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1378_, v_a_1379_);
lean_dec(v_a_1379_);
lean_dec_ref(v_m_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(lean_object* v_s_1381_){
_start:
{
lean_object* v___x_1383_; lean_object* v_putStr_1384_; lean_object* v___x_1385_; 
v___x_1383_ = lean_get_stdout();
v_putStr_1384_ = lean_ctor_get(v___x_1383_, 4);
lean_inc_ref(v_putStr_1384_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = lean_apply_2(v_putStr_1384_, v_s_1381_, lean_box(0));
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2___boxed(lean_object* v_s_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v_s_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(lean_object* v_s_1389_){
_start:
{
uint32_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = 10;
v___x_1392_ = lean_string_push(v_s_1389_, v___x_1391_);
v___x_1393_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1___boxed(lean_object* v_s_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v_s_1394_);
return v_res_1396_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1401_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1402_ = lean_unsigned_to_nat(18u);
v___x_1403_ = lean_unsigned_to_nat(114u);
v___x_1404_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2));
v___x_1405_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1406_ = l_mkPanicMessageWithDecl(v___x_1405_, v___x_1404_, v___x_1403_, v___x_1402_, v___x_1401_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName(lean_object* v_n_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_visitedNames_1415_; lean_object* v___x_1416_; 
v_visitedNames_1415_ = lean_ctor_get(v_a_1413_, 0);
v___x_1416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_visitedNames_1415_, v_n_1411_);
if (lean_obj_tag(v___x_1416_) == 1)
{
lean_object* v_val_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_n_1411_);
v_val_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_val_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v_val_1417_);
lean_ctor_set(v___x_1421_, 1, v_a_1413_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1421_);
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_object* v___x_1426_; lean_object* v_fst_1428_; lean_object* v_snd_1429_; 
lean_dec(v___x_1416_);
v___x_1426_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0));
switch(lean_obj_tag(v_n_1411_))
{
case 0:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4, &l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4);
v___x_1471_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1470_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v_fst_1473_; lean_object* v_snd_1474_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v_fst_1473_ = lean_ctor_get(v_a_1472_, 0);
lean_inc(v_fst_1473_);
v_snd_1474_ = lean_ctor_get(v_a_1472_, 1);
lean_inc(v_snd_1474_);
lean_dec(v_a_1472_);
v_fst_1428_ = v_fst_1473_;
v_snd_1429_ = v_snd_1474_;
goto v___jp_1427_;
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_a_1475_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1471_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1471_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
case 1:
{
lean_object* v_pre_1483_; lean_object* v_str_1484_; lean_object* v___x_1485_; 
v_pre_1483_ = lean_ctor_get(v_n_1411_, 0);
v_str_1484_ = lean_ctor_get(v_n_1411_, 1);
lean_inc(v_pre_1483_);
v___x_1485_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1483_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1514_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1514_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1514_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_fst_1490_; lean_object* v_snd_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1513_; 
v_fst_1490_ = lean_ctor_get(v_a_1486_, 0);
v_snd_1491_ = lean_ctor_get(v_a_1486_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_a_1486_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1493_ = v_a_1486_;
v_isShared_1494_ = v_isSharedCheck_1513_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_snd_1491_);
lean_inc(v_fst_1490_);
lean_dec(v_a_1486_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1513_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1495_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5));
v___x_1496_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1497_ = l_Lean_JsonNumber_fromNat(v_fst_1490_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 2);
lean_ctor_set(v___x_1488_, 0, v___x_1497_);
v___x_1499_ = v___x_1488_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1499_);
lean_ctor_set(v___x_1493_, 0, v___x_1496_);
v___x_1501_ = v___x_1493_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_inc_ref(v_str_1484_);
v___x_1502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_str_1484_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1495_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1501_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l_Lean_Json_mkObj(v___x_1506_);
lean_dec_ref_known(v___x_1506_, 2);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1495_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1504_);
v___x_1510_ = l_Lean_Json_mkObj(v___x_1509_);
lean_dec_ref_known(v___x_1509_, 2);
v_fst_1428_ = v___x_1510_;
v_snd_1429_ = v_snd_1491_;
goto v___jp_1427_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1411_, 2);
return v___x_1485_;
}
}
default: 
{
lean_object* v_pre_1515_; lean_object* v_i_1516_; lean_object* v___x_1517_; 
v_pre_1515_ = lean_ctor_get(v_n_1411_, 0);
v_i_1516_ = lean_ctor_get(v_n_1411_, 1);
lean_inc(v_pre_1515_);
v___x_1517_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1515_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1548_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1548_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1548_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_fst_1522_; lean_object* v_snd_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1547_; 
v_fst_1522_ = lean_ctor_get(v_a_1518_, 0);
v_snd_1523_ = lean_ctor_get(v_a_1518_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_a_1518_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1525_ = v_a_1518_;
v_isShared_1526_ = v_isSharedCheck_1547_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_snd_1523_);
lean_inc(v_fst_1522_);
lean_dec(v_a_1518_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1547_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1527_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7));
v___x_1528_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1529_ = l_Lean_JsonNumber_fromNat(v_fst_1522_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 2);
lean_ctor_set(v___x_1520_, 0, v___x_1529_);
v___x_1531_ = v___x_1520_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 1, v___x_1531_);
lean_ctor_set(v___x_1525_, 0, v___x_1528_);
v___x_1533_ = v___x_1525_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1534_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8));
lean_inc(v_i_1516_);
v___x_1535_ = l_Lean_JsonNumber_fromNat(v_i_1516_);
v___x_1536_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1534_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1533_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_Json_mkObj(v___x_1540_);
lean_dec_ref_known(v___x_1540_, 2);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1527_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___x_1538_);
v___x_1544_ = l_Lean_Json_mkObj(v___x_1543_);
lean_dec_ref_known(v___x_1543_, 2);
v_fst_1428_ = v___x_1544_;
v_snd_1429_ = v_snd_1523_;
goto v___jp_1427_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1411_, 2);
return v___x_1517_;
}
}
}
v___jp_1427_:
{
lean_object* v_visitedNames_1430_; lean_object* v_visitedLevels_1431_; lean_object* v_visitedExprs_1432_; lean_object* v_visitedConstants_1433_; lean_object* v_noMDataExprs_1434_; uint8_t v_exportMData_1435_; uint8_t v_exportUnsafe_1436_; uint8_t v_ignoreMissing_1437_; lean_object* v_recursorMap_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1469_; 
v_visitedNames_1430_ = lean_ctor_get(v_snd_1429_, 0);
v_visitedLevels_1431_ = lean_ctor_get(v_snd_1429_, 1);
v_visitedExprs_1432_ = lean_ctor_get(v_snd_1429_, 2);
v_visitedConstants_1433_ = lean_ctor_get(v_snd_1429_, 3);
v_noMDataExprs_1434_ = lean_ctor_get(v_snd_1429_, 4);
v_exportMData_1435_ = lean_ctor_get_uint8(v_snd_1429_, sizeof(void*)*6);
v_exportUnsafe_1436_ = lean_ctor_get_uint8(v_snd_1429_, sizeof(void*)*6 + 1);
v_ignoreMissing_1437_ = lean_ctor_get_uint8(v_snd_1429_, sizeof(void*)*6 + 2);
v_recursorMap_1438_ = lean_ctor_get(v_snd_1429_, 5);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_snd_1429_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1440_ = v_snd_1429_;
v_isShared_1441_ = v_isSharedCheck_1469_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_recursorMap_1438_);
lean_inc(v_noMDataExprs_1434_);
lean_inc(v_visitedConstants_1433_);
lean_inc(v_visitedExprs_1432_);
lean_inc(v_visitedLevels_1431_);
lean_inc(v_visitedNames_1430_);
lean_dec(v_snd_1429_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1469_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v_size_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_size_1442_ = lean_ctor_get(v_visitedNames_1430_, 0);
lean_inc_n(v_size_1442_, 2);
v___x_1443_ = l_Lean_JsonNumber_fromNat(v_size_1442_);
v___x_1444_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
v___x_1445_ = l_Lean_Json_setObjVal_x21(v_fst_1428_, v___x_1426_, v___x_1444_);
v___x_1446_ = l_Lean_Json_compress(v___x_1445_);
v___x_1447_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1446_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1459_; 
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v___x_1447_, 0);
lean_dec(v_unused_1460_);
v___x_1449_ = v___x_1447_;
v_isShared_1450_ = v_isSharedCheck_1459_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v___x_1447_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1459_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
lean_inc(v_size_1442_);
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v_visitedNames_1430_, v_n_1411_, v_size_1442_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1451_);
v___x_1453_ = v___x_1440_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_visitedLevels_1431_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_visitedExprs_1432_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v_visitedConstants_1433_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v_noMDataExprs_1434_);
lean_ctor_set(v_reuseFailAlloc_1458_, 5, v_recursorMap_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1458_, sizeof(void*)*6, v_exportMData_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1458_, sizeof(void*)*6 + 1, v_exportUnsafe_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1458_, sizeof(void*)*6 + 2, v_ignoreMissing_1437_);
v___x_1453_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_size_1442_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1454_);
v___x_1456_ = v___x_1449_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
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
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_size_1442_);
lean_del_object(v___x_1440_);
lean_dec(v_recursorMap_1438_);
lean_dec_ref(v_noMDataExprs_1434_);
lean_dec_ref(v_visitedConstants_1433_);
lean_dec_ref(v_visitedExprs_1432_);
lean_dec_ref(v_visitedLevels_1431_);
lean_dec_ref(v_visitedNames_1430_);
lean_dec(v_n_1411_);
v_a_1461_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1447_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1447_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___boxed(lean_object* v_n_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_n_1549_, v_a_1550_, v_a_1551_);
lean_dec_ref(v_a_1550_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(lean_object* v_00_u03b2_1554_, lean_object* v_m_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1555_, v_a_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___boxed(lean_object* v_00_u03b2_1558_, lean_object* v_m_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(v_00_u03b2_1558_, v_m_1559_, v_a_1560_);
lean_dec(v_a_1560_);
lean_dec_ref(v_m_1559_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(lean_object* v_00_u03b2_1562_, lean_object* v_a_1563_, lean_object* v_x_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1563_, v_x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1566_, lean_object* v_a_1567_, lean_object* v_x_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(v_00_u03b2_1566_, v_a_1567_, v_x_1568_);
lean_dec(v_x_1568_);
lean_dec(v_a_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(lean_object* v_a_1570_, lean_object* v_x_1571_){
_start:
{
if (lean_obj_tag(v_x_1571_) == 0)
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_box(0);
return v___x_1572_;
}
else
{
lean_object* v_key_1573_; lean_object* v_value_1574_; lean_object* v_tail_1575_; uint8_t v___x_1576_; 
v_key_1573_ = lean_ctor_get(v_x_1571_, 0);
v_value_1574_ = lean_ctor_get(v_x_1571_, 1);
v_tail_1575_ = lean_ctor_get(v_x_1571_, 2);
v___x_1576_ = lean_level_eq(v_key_1573_, v_a_1570_);
if (v___x_1576_ == 0)
{
v_x_1571_ = v_tail_1575_;
goto _start;
}
else
{
lean_object* v___x_1578_; 
lean_inc(v_value_1574_);
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_value_1574_);
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg___boxed(lean_object* v_a_1579_, lean_object* v_x_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1579_, v_x_1580_);
lean_dec(v_x_1580_);
lean_dec(v_a_1579_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(lean_object* v_m_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_buckets_1584_; lean_object* v___x_1585_; uint64_t v___x_1586_; uint64_t v___x_1587_; uint64_t v___x_1588_; uint64_t v_fold_1589_; uint64_t v___x_1590_; uint64_t v___x_1591_; uint64_t v___x_1592_; size_t v___x_1593_; size_t v___x_1594_; size_t v___x_1595_; size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_buckets_1584_ = lean_ctor_get(v_m_1582_, 1);
v___x_1585_ = lean_array_get_size(v_buckets_1584_);
v___x_1586_ = l_Lean_Level_hash(v_a_1583_);
v___x_1587_ = 32ULL;
v___x_1588_ = lean_uint64_shift_right(v___x_1586_, v___x_1587_);
v_fold_1589_ = lean_uint64_xor(v___x_1586_, v___x_1588_);
v___x_1590_ = 16ULL;
v___x_1591_ = lean_uint64_shift_right(v_fold_1589_, v___x_1590_);
v___x_1592_ = lean_uint64_xor(v_fold_1589_, v___x_1591_);
v___x_1593_ = lean_uint64_to_usize(v___x_1592_);
v___x_1594_ = lean_usize_of_nat(v___x_1585_);
v___x_1595_ = ((size_t)1ULL);
v___x_1596_ = lean_usize_sub(v___x_1594_, v___x_1595_);
v___x_1597_ = lean_usize_land(v___x_1593_, v___x_1596_);
v___x_1598_ = lean_array_uget_borrowed(v_buckets_1584_, v___x_1597_);
v___x_1599_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1583_, v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg___boxed(lean_object* v_m_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_m_1600_);
return v_res_1602_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1609_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1610_ = lean_unsigned_to_nat(23u);
v___x_1611_ = lean_unsigned_to_nat(132u);
v___x_1612_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5));
v___x_1613_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1614_ = l_mkPanicMessageWithDecl(v___x_1613_, v___x_1612_, v___x_1611_, v___x_1610_, v___x_1609_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel(lean_object* v_l_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_visitedLevels_1619_; lean_object* v___x_1620_; 
v_visitedLevels_1619_ = lean_ctor_get(v_a_1617_, 1);
v___x_1620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_visitedLevels_1619_, v_l_1615_);
if (lean_obj_tag(v___x_1620_) == 1)
{
lean_object* v_val_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_l_1615_);
v_val_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_val_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_val_1621_);
lean_ctor_set(v___x_1625_, 1, v_a_1617_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set_tag(v___x_1623_, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1625_);
v___x_1627_ = v___x_1623_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
else
{
lean_object* v___x_1630_; lean_object* v_fst_1632_; lean_object* v_snd_1633_; 
lean_dec(v___x_1620_);
v___x_1630_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0));
switch(lean_obj_tag(v_l_1615_))
{
case 1:
{
lean_object* v_a_1674_; lean_object* v___x_1675_; 
v_a_1674_ = lean_ctor_get(v_l_1615_, 0);
lean_inc(v_a_1674_);
v___x_1675_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1674_, v_a_1616_, v_a_1617_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1697_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1697_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1697_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v_fst_1680_; lean_object* v_snd_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1696_; 
v_fst_1680_ = lean_ctor_get(v_a_1676_, 0);
v_snd_1681_ = lean_ctor_get(v_a_1676_, 1);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_a_1676_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1683_ = v_a_1676_;
v_isShared_1684_ = v_isSharedCheck_1696_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_snd_1681_);
lean_inc(v_fst_1680_);
lean_dec(v_a_1676_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1696_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1685_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1));
v___x_1686_ = l_Lean_JsonNumber_fromNat(v_fst_1680_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 2);
lean_ctor_set(v___x_1678_, 0, v___x_1686_);
v___x_1688_ = v___x_1678_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 1, v___x_1688_);
lean_ctor_set(v___x_1683_, 0, v___x_1685_);
v___x_1690_ = v___x_1683_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = lean_box(0);
v___x_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1690_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = l_Lean_Json_mkObj(v___x_1692_);
lean_dec_ref_known(v___x_1692_, 2);
v_fst_1632_ = v___x_1693_;
v_snd_1633_ = v_snd_1681_;
goto v___jp_1631_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1615_, 1);
return v___x_1675_;
}
}
case 2:
{
lean_object* v_a_1698_; lean_object* v_a_1699_; lean_object* v___x_1700_; 
v_a_1698_ = lean_ctor_get(v_l_1615_, 0);
v_a_1699_ = lean_ctor_get(v_l_1615_, 1);
lean_inc(v_a_1698_);
v___x_1700_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1698_, v_a_1616_, v_a_1617_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1745_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1745_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1745_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_fst_1705_; lean_object* v_snd_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1744_; 
v_fst_1705_ = lean_ctor_get(v_a_1701_, 0);
v_snd_1706_ = lean_ctor_get(v_a_1701_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_a_1701_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1708_ = v_a_1701_;
v_isShared_1709_ = v_isSharedCheck_1744_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snd_1706_);
lean_inc(v_fst_1705_);
lean_dec(v_a_1701_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1744_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; 
lean_inc(v_a_1699_);
v___x_1710_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1699_, v_a_1616_, v_snd_1706_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1743_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1743_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1743_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_fst_1715_; lean_object* v_snd_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1742_; 
v_fst_1715_ = lean_ctor_get(v_a_1711_, 0);
v_snd_1716_ = lean_ctor_get(v_a_1711_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_a_1711_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1718_ = v_a_1711_;
v_isShared_1719_ = v_isSharedCheck_1742_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_snd_1716_);
lean_inc(v_fst_1715_);
lean_dec(v_a_1711_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1742_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1720_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2));
v___x_1721_ = l_Lean_JsonNumber_fromNat(v_fst_1705_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 2);
lean_ctor_set(v___x_1713_, 0, v___x_1721_);
v___x_1723_ = v___x_1713_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = l_Lean_JsonNumber_fromNat(v_fst_1715_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 2);
lean_ctor_set(v___x_1703_, 0, v___x_1724_);
v___x_1726_ = v___x_1703_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1727_ = lean_unsigned_to_nat(2u);
v___x_1728_ = lean_mk_empty_array_with_capacity(v___x_1727_);
v___x_1729_ = lean_array_push(v___x_1728_, v___x_1723_);
v___x_1730_ = lean_array_push(v___x_1729_, v___x_1726_);
v___x_1731_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 1, v___x_1731_);
lean_ctor_set(v___x_1718_, 0, v___x_1720_);
v___x_1733_ = v___x_1718_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1734_ = lean_box(0);
if (v_isShared_1709_ == 0)
{
lean_ctor_set_tag(v___x_1708_, 1);
lean_ctor_set(v___x_1708_, 1, v___x_1734_);
lean_ctor_set(v___x_1708_, 0, v___x_1733_);
v___x_1736_ = v___x_1708_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Json_mkObj(v___x_1736_);
lean_dec_ref(v___x_1736_);
v_fst_1632_ = v___x_1737_;
v_snd_1633_ = v_snd_1716_;
goto v___jp_1631_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1708_);
lean_dec(v_fst_1705_);
lean_del_object(v___x_1703_);
lean_dec_ref_known(v_l_1615_, 2);
return v___x_1710_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1615_, 2);
return v___x_1700_;
}
}
case 3:
{
lean_object* v_a_1746_; lean_object* v_a_1747_; lean_object* v___x_1748_; 
v_a_1746_ = lean_ctor_get(v_l_1615_, 0);
v_a_1747_ = lean_ctor_get(v_l_1615_, 1);
lean_inc(v_a_1746_);
v___x_1748_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1746_, v_a_1616_, v_a_1617_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1793_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1793_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1793_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1792_; 
v_fst_1753_ = lean_ctor_get(v_a_1749_, 0);
v_snd_1754_ = lean_ctor_get(v_a_1749_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_a_1749_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1756_ = v_a_1749_;
v_isShared_1757_ = v_isSharedCheck_1792_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snd_1754_);
lean_inc(v_fst_1753_);
lean_dec(v_a_1749_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1792_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; 
lean_inc(v_a_1747_);
v___x_1758_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1747_, v_a_1616_, v_snd_1754_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1791_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1791_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1791_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_fst_1763_; lean_object* v_snd_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1790_; 
v_fst_1763_ = lean_ctor_get(v_a_1759_, 0);
v_snd_1764_ = lean_ctor_get(v_a_1759_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_a_1759_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1766_ = v_a_1759_;
v_isShared_1767_ = v_isSharedCheck_1790_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_snd_1764_);
lean_inc(v_fst_1763_);
lean_dec(v_a_1759_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1790_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1768_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3));
v___x_1769_ = l_Lean_JsonNumber_fromNat(v_fst_1753_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 2);
lean_ctor_set(v___x_1761_, 0, v___x_1769_);
v___x_1771_ = v___x_1761_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = l_Lean_JsonNumber_fromNat(v_fst_1763_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 2);
lean_ctor_set(v___x_1751_, 0, v___x_1772_);
v___x_1774_ = v___x_1751_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1775_ = lean_unsigned_to_nat(2u);
v___x_1776_ = lean_mk_empty_array_with_capacity(v___x_1775_);
v___x_1777_ = lean_array_push(v___x_1776_, v___x_1771_);
v___x_1778_ = lean_array_push(v___x_1777_, v___x_1774_);
v___x_1779_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v___x_1779_);
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1781_ = v___x_1766_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_box(0);
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 1);
lean_ctor_set(v___x_1756_, 1, v___x_1782_);
lean_ctor_set(v___x_1756_, 0, v___x_1781_);
v___x_1784_ = v___x_1756_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_Json_mkObj(v___x_1784_);
lean_dec_ref(v___x_1784_);
v_fst_1632_ = v___x_1785_;
v_snd_1633_ = v_snd_1764_;
goto v___jp_1631_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1756_);
lean_dec(v_fst_1753_);
lean_del_object(v___x_1751_);
lean_dec_ref_known(v_l_1615_, 2);
return v___x_1758_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1615_, 2);
return v___x_1748_;
}
}
case 4:
{
lean_object* v_a_1794_; lean_object* v___x_1795_; 
v_a_1794_ = lean_ctor_get(v_l_1615_, 0);
lean_inc(v_a_1794_);
v___x_1795_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_a_1794_, v_a_1616_, v_a_1617_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1817_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1817_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1817_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_fst_1800_; lean_object* v_snd_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1816_; 
v_fst_1800_ = lean_ctor_get(v_a_1796_, 0);
v_snd_1801_ = lean_ctor_get(v_a_1796_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_a_1796_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1803_ = v_a_1796_;
v_isShared_1804_ = v_isSharedCheck_1816_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_snd_1801_);
lean_inc(v_fst_1800_);
lean_dec(v_a_1796_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1816_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1805_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4));
v___x_1806_ = l_Lean_JsonNumber_fromNat(v_fst_1800_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 2);
lean_ctor_set(v___x_1798_, 0, v___x_1806_);
v___x_1808_ = v___x_1798_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___x_1808_);
lean_ctor_set(v___x_1803_, 0, v___x_1805_);
v___x_1810_ = v___x_1803_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_Json_mkObj(v___x_1812_);
lean_dec_ref_known(v___x_1812_, 2);
v_fst_1632_ = v___x_1813_;
v_snd_1633_ = v_snd_1801_;
goto v___jp_1631_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1615_, 1);
return v___x_1795_;
}
}
default: 
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6, &l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6);
v___x_1819_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1818_, v_a_1616_, v_a_1617_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v_fst_1821_; lean_object* v_snd_1822_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
v_fst_1821_ = lean_ctor_get(v_a_1820_, 0);
lean_inc(v_fst_1821_);
v_snd_1822_ = lean_ctor_get(v_a_1820_, 1);
lean_inc(v_snd_1822_);
lean_dec(v_a_1820_);
v_fst_1632_ = v_fst_1821_;
v_snd_1633_ = v_snd_1822_;
goto v___jp_1631_;
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_l_1615_);
v_a_1823_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1819_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1819_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
v___jp_1631_:
{
lean_object* v_visitedLevels_1634_; lean_object* v_visitedNames_1635_; lean_object* v_visitedExprs_1636_; lean_object* v_visitedConstants_1637_; lean_object* v_noMDataExprs_1638_; uint8_t v_exportMData_1639_; uint8_t v_exportUnsafe_1640_; uint8_t v_ignoreMissing_1641_; lean_object* v_recursorMap_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1673_; 
v_visitedLevels_1634_ = lean_ctor_get(v_snd_1633_, 1);
v_visitedNames_1635_ = lean_ctor_get(v_snd_1633_, 0);
v_visitedExprs_1636_ = lean_ctor_get(v_snd_1633_, 2);
v_visitedConstants_1637_ = lean_ctor_get(v_snd_1633_, 3);
v_noMDataExprs_1638_ = lean_ctor_get(v_snd_1633_, 4);
v_exportMData_1639_ = lean_ctor_get_uint8(v_snd_1633_, sizeof(void*)*6);
v_exportUnsafe_1640_ = lean_ctor_get_uint8(v_snd_1633_, sizeof(void*)*6 + 1);
v_ignoreMissing_1641_ = lean_ctor_get_uint8(v_snd_1633_, sizeof(void*)*6 + 2);
v_recursorMap_1642_ = lean_ctor_get(v_snd_1633_, 5);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_snd_1633_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1644_ = v_snd_1633_;
v_isShared_1645_ = v_isSharedCheck_1673_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_recursorMap_1642_);
lean_inc(v_noMDataExprs_1638_);
lean_inc(v_visitedConstants_1637_);
lean_inc(v_visitedExprs_1636_);
lean_inc(v_visitedLevels_1634_);
lean_inc(v_visitedNames_1635_);
lean_dec(v_snd_1633_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1673_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_size_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_size_1646_ = lean_ctor_get(v_visitedLevels_1634_, 0);
lean_inc_n(v_size_1646_, 2);
v___x_1647_ = l_Lean_JsonNumber_fromNat(v_size_1646_);
v___x_1648_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
v___x_1649_ = l_Lean_Json_setObjVal_x21(v_fst_1632_, v___x_1630_, v___x_1648_);
v___x_1650_ = l_Lean_Json_compress(v___x_1649_);
v___x_1651_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1650_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1663_; 
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v___x_1651_, 0);
lean_dec(v_unused_1664_);
v___x_1653_ = v___x_1651_;
v_isShared_1654_ = v_isSharedCheck_1663_;
goto v_resetjp_1652_;
}
else
{
lean_dec(v___x_1651_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1663_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
lean_inc(v_size_1646_);
v___x_1655_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v_visitedLevels_1634_, v_l_1615_, v_size_1646_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 1, v___x_1655_);
v___x_1657_ = v___x_1644_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_visitedNames_1635_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_visitedExprs_1636_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v_visitedConstants_1637_);
lean_ctor_set(v_reuseFailAlloc_1662_, 4, v_noMDataExprs_1638_);
lean_ctor_set(v_reuseFailAlloc_1662_, 5, v_recursorMap_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1662_, sizeof(void*)*6, v_exportMData_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1662_, sizeof(void*)*6 + 1, v_exportUnsafe_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1662_, sizeof(void*)*6 + 2, v_ignoreMissing_1641_);
v___x_1657_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v_size_1646_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1658_);
v___x_1660_ = v___x_1653_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
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
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_size_1646_);
lean_del_object(v___x_1644_);
lean_dec(v_recursorMap_1642_);
lean_dec_ref(v_noMDataExprs_1638_);
lean_dec_ref(v_visitedConstants_1637_);
lean_dec_ref(v_visitedExprs_1636_);
lean_dec_ref(v_visitedNames_1635_);
lean_dec_ref(v_visitedLevels_1634_);
lean_dec(v_l_1615_);
v_a_1665_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1651_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1651_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___boxed(lean_object* v_l_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_l_1831_, v_a_1832_, v_a_1833_);
lean_dec_ref(v_a_1832_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(lean_object* v_00_u03b2_1836_, lean_object* v_m_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1837_, v_a_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___boxed(lean_object* v_00_u03b2_1840_, lean_object* v_m_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(v_00_u03b2_1840_, v_m_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_m_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(lean_object* v_00_u03b2_1844_, lean_object* v_a_1845_, lean_object* v_x_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1845_, v_x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1848_, lean_object* v_a_1849_, lean_object* v_x_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(v_00_u03b2_1848_, v_a_1849_, v_x_1850_);
lean_dec(v_x_1850_);
lean_dec(v_a_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
if (lean_obj_tag(v_a_1852_) == 0)
{
lean_object* v___x_1854_; 
v___x_1854_ = l_List_reverse___redArg(v_a_1853_);
return v___x_1854_;
}
else
{
lean_object* v_head_1855_; lean_object* v_tail_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1865_; 
v_head_1855_ = lean_ctor_get(v_a_1852_, 0);
v_tail_1856_ = lean_ctor_get(v_a_1852_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_a_1852_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1858_ = v_a_1852_;
v_isShared_1859_ = v_isSharedCheck_1865_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_tail_1856_);
lean_inc(v_head_1855_);
lean_dec(v_a_1852_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1865_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1860_ = l_Lean_Level_param___override(v_head_1855_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v_a_1853_);
lean_ctor_set(v___x_1858_, 0, v___x_1860_);
v___x_1862_ = v___x_1858_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_a_1853_);
v___x_1862_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
v_a_1852_ = v_tail_1856_;
v_a_1853_ = v___x_1862_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(size_t v_sz_1866_, size_t v_i_1867_, lean_object* v_bs_1868_){
_start:
{
uint8_t v___x_1869_; 
v___x_1869_ = lean_usize_dec_lt(v_i_1867_, v_sz_1866_);
if (v___x_1869_ == 0)
{
return v_bs_1868_;
}
else
{
lean_object* v_v_1870_; lean_object* v___x_1871_; lean_object* v_bs_x27_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; size_t v___x_1875_; size_t v___x_1876_; lean_object* v___x_1877_; 
v_v_1870_ = lean_array_uget(v_bs_1868_, v_i_1867_);
v___x_1871_ = lean_unsigned_to_nat(0u);
v_bs_x27_1872_ = lean_array_uset(v_bs_1868_, v_i_1867_, v___x_1871_);
v___x_1873_ = l_Lean_JsonNumber_fromNat(v_v_1870_);
v___x_1874_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
v___x_1875_ = ((size_t)1ULL);
v___x_1876_ = lean_usize_add(v_i_1867_, v___x_1875_);
v___x_1877_ = lean_array_uset(v_bs_x27_1872_, v_i_1867_, v___x_1874_);
v_i_1867_ = v___x_1876_;
v_bs_1868_ = v___x_1877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1879_, lean_object* v_i_1880_, lean_object* v_bs_1881_){
_start:
{
size_t v_sz_boxed_1882_; size_t v_i_boxed_1883_; lean_object* v_res_1884_; 
v_sz_boxed_1882_ = lean_unbox_usize(v_sz_1879_);
lean_dec(v_sz_1879_);
v_i_boxed_1883_ = lean_unbox_usize(v_i_1880_);
lean_dec(v_i_1880_);
v_res_1884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_boxed_1882_, v_i_boxed_1883_, v_bs_1881_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(lean_object* v_a_1885_){
_start:
{
size_t v_sz_1886_; size_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_sz_1886_ = lean_array_size(v_a_1885_);
v___x_1887_ = ((size_t)0ULL);
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_1886_, v___x_1887_, v_a_1885_);
v___x_1889_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(lean_object* v_a_1890_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_array_mk(v_a_1890_);
v___x_1892_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
if (lean_obj_tag(v_x_1893_) == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = l_List_reverse___redArg(v_x_1894_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v___y_1896_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
else
{
lean_object* v_head_1901_; lean_object* v_tail_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1922_; 
v_head_1901_ = lean_ctor_get(v_x_1893_, 0);
v_tail_1902_ = lean_ctor_get(v_x_1893_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_x_1893_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1904_ = v_x_1893_;
v_isShared_1905_ = v_isSharedCheck_1922_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_tail_1902_);
lean_inc(v_head_1901_);
lean_dec(v_x_1893_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1922_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; 
v___x_1906_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_head_1901_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v_fst_1908_; lean_object* v_snd_1909_; lean_object* v___x_1911_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v_fst_1908_ = lean_ctor_get(v_a_1907_, 0);
lean_inc(v_fst_1908_);
v_snd_1909_ = lean_ctor_get(v_a_1907_, 1);
lean_inc(v_snd_1909_);
lean_dec(v_a_1907_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 1, v_x_1894_);
lean_ctor_set(v___x_1904_, 0, v_fst_1908_);
v___x_1911_ = v___x_1904_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_fst_1908_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_x_1894_);
v___x_1911_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
v_x_1893_ = v_tail_1902_;
v_x_1894_ = v___x_1911_;
v___y_1896_ = v_snd_1909_;
goto _start;
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_del_object(v___x_1904_);
lean_dec(v_tail_1902_);
lean_dec(v_x_1894_);
v_a_1914_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1906_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1906_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2___boxed(lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_x_1923_, v_x_1924_, v___y_1925_, v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(lean_object* v_x_1929_, lean_object* v_x_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
if (lean_obj_tag(v_x_1929_) == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = l_List_reverse___redArg(v_x_1930_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v___y_1932_);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
else
{
lean_object* v_head_1937_; lean_object* v_tail_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1958_; 
v_head_1937_ = lean_ctor_get(v_x_1929_, 0);
v_tail_1938_ = lean_ctor_get(v_x_1929_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_x_1929_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1940_ = v_x_1929_;
v_isShared_1941_ = v_isSharedCheck_1958_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_tail_1938_);
lean_inc(v_head_1937_);
lean_dec(v_x_1929_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1958_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; 
v___x_1942_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_head_1937_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v_fst_1944_; lean_object* v_snd_1945_; lean_object* v___x_1947_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v_fst_1944_ = lean_ctor_get(v_a_1943_, 0);
lean_inc(v_fst_1944_);
v_snd_1945_ = lean_ctor_get(v_a_1943_, 1);
lean_inc(v_snd_1945_);
lean_dec(v_a_1943_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 1, v_x_1930_);
lean_ctor_set(v___x_1940_, 0, v_fst_1944_);
v___x_1947_ = v___x_1940_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_fst_1944_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_x_1930_);
v___x_1947_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
v_x_1929_ = v_tail_1938_;
v_x_1930_ = v___x_1947_;
v___y_1932_ = v_snd_1945_;
goto _start;
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_del_object(v___x_1940_);
lean_dec(v_tail_1938_);
lean_dec(v_x_1930_);
v_a_1950_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1942_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1942_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0___boxed(lean_object* v_x_1959_, lean_object* v_x_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_x_1959_, v_x_1960_, v___y_1961_, v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams(lean_object* v_uparams_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_box(0);
lean_inc(v_uparams_1965_);
v___x_1970_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_1965_, v___x_1969_, v_a_1966_, v_a_1967_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v_fst_1972_; lean_object* v_snd_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v_fst_1972_ = lean_ctor_get(v_a_1971_, 0);
lean_inc(v_fst_1972_);
v_snd_1973_ = lean_ctor_get(v_a_1971_, 1);
lean_inc(v_snd_1973_);
lean_dec(v_a_1971_);
v___x_1974_ = l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(v_uparams_1965_, v___x_1969_);
v___x_1975_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v___x_1974_, v___x_1969_, v_a_1966_, v_snd_1973_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1993_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1993_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1993_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_snd_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1991_; 
v_snd_1980_ = lean_ctor_get(v_a_1976_, 1);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_a_1976_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; 
v_unused_1992_ = lean_ctor_get(v_a_1976_, 0);
lean_dec(v_unused_1992_);
v___x_1982_ = v_a_1976_;
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_snd_1980_);
lean_dec(v_a_1976_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_1972_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1984_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_snd_1980_);
v___x_1986_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1988_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1986_);
v___x_1988_ = v___x_1978_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v_fst_1972_);
v_a_1994_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1975_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1975_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec(v_uparams_1965_);
v_a_2002_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1970_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1970_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams___boxed(lean_object* v_uparams_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_uparams_2010_, v_a_2011_, v_a_2012_);
lean_dec_ref(v_a_2011_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames(lean_object* v_uparams_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_box(0);
v___x_2020_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_2015_, v___x_2019_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2038_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2038_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2038_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v_fst_2025_; lean_object* v_snd_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2037_; 
v_fst_2025_ = lean_ctor_get(v_a_2021_, 0);
v_snd_2026_ = lean_ctor_get(v_a_2021_, 1);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_a_2021_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2028_ = v_a_2021_;
v_isShared_2029_ = v_isSharedCheck_2037_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_snd_2026_);
lean_inc(v_fst_2025_);
lean_dec(v_a_2021_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2037_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2030_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_2025_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2030_);
v___x_2032_ = v___x_2028_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_snd_2026_);
v___x_2032_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2034_; 
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2032_);
v___x_2034_ = v___x_2023_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
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
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v_a_2039_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2020_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2020_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames___boxed(lean_object* v_uparams_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_uparams_2047_, v_a_2048_, v_a_2049_);
lean_dec_ref(v_a_2048_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(lean_object* v_msg_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2056_; lean_object* v___f_2057_; lean_object* v___f_2058_; lean_object* v___f_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___f_2069_; lean_object* v___x_11487__overap_2070_; lean_object* v___x_2071_; 
v___x_2056_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2057_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2057_, 0, v___x_2056_);
v___f_2058_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2058_, 0, v___x_2056_);
v___f_2059_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2059_, 0, v___x_2056_);
v___f_2060_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2060_, 0, v___x_2056_);
v___x_2061_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2061_, 0, lean_box(0));
lean_closure_set(v___x_2061_, 1, lean_box(0));
lean_closure_set(v___x_2061_, 2, v___x_2056_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v___f_2057_);
v___x_2063_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2063_, 0, lean_box(0));
lean_closure_set(v___x_2063_, 1, lean_box(0));
lean_closure_set(v___x_2063_, 2, v___x_2056_);
v___x_2064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
lean_ctor_set(v___x_2064_, 2, v___f_2058_);
lean_ctor_set(v___x_2064_, 3, v___f_2059_);
lean_ctor_set(v___x_2064_, 4, v___f_2060_);
v___x_2065_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2065_, 0, lean_box(0));
lean_closure_set(v___x_2065_, 1, lean_box(0));
lean_closure_set(v___x_2065_, 2, v___x_2056_);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2064_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = l_Lean_instInhabitedExpr;
v___x_2068_ = l_instInhabitedOfMonad___redArg(v___x_2066_, v___x_2067_);
v___f_2069_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2069_, 0, v___x_2068_);
v___x_11487__overap_2070_ = lean_panic_fn_borrowed(v___f_2069_, v_msg_2052_);
lean_dec_ref(v___f_2069_);
lean_inc_ref(v___y_2053_);
v___x_2071_ = lean_apply_3(v___x_11487__overap_2070_, v___y_2053_, v___y_2054_, lean_box(0));
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2___boxed(lean_object* v_msg_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v_msg_2072_, v___y_2073_, v___y_2074_);
lean_dec_ref(v___y_2073_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(lean_object* v_a_2077_, lean_object* v_b_2078_, lean_object* v_x_2079_){
_start:
{
if (lean_obj_tag(v_x_2079_) == 0)
{
lean_dec(v_b_2078_);
lean_dec_ref(v_a_2077_);
return v_x_2079_;
}
else
{
lean_object* v_key_2080_; lean_object* v_value_2081_; lean_object* v_tail_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2094_; 
v_key_2080_ = lean_ctor_get(v_x_2079_, 0);
v_value_2081_ = lean_ctor_get(v_x_2079_, 1);
v_tail_2082_ = lean_ctor_get(v_x_2079_, 2);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_x_2079_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2084_ = v_x_2079_;
v_isShared_2085_ = v_isSharedCheck_2094_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_tail_2082_);
lean_inc(v_value_2081_);
lean_inc(v_key_2080_);
lean_dec(v_x_2079_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2094_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_expr_eqv(v_key_2080_, v_a_2077_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2077_, v_b_2078_, v_tail_2082_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 2, v___x_2087_);
v___x_2089_ = v___x_2084_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_key_2080_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_value_2081_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
else
{
lean_object* v___x_2092_; 
lean_dec(v_value_2081_);
lean_dec(v_key_2080_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v_b_2078_);
lean_ctor_set(v___x_2084_, 0, v_a_2077_);
v___x_2092_ = v___x_2084_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2077_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_b_2078_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_tail_2082_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_2095_, lean_object* v_x_2096_){
_start:
{
if (lean_obj_tag(v_x_2096_) == 0)
{
return v_x_2095_;
}
else
{
lean_object* v_key_2097_; lean_object* v_value_2098_; lean_object* v_tail_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2122_; 
v_key_2097_ = lean_ctor_get(v_x_2096_, 0);
v_value_2098_ = lean_ctor_get(v_x_2096_, 1);
v_tail_2099_ = lean_ctor_get(v_x_2096_, 2);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_x_2096_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2101_ = v_x_2096_;
v_isShared_2102_ = v_isSharedCheck_2122_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_tail_2099_);
lean_inc(v_value_2098_);
lean_inc(v_key_2097_);
lean_dec(v_x_2096_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2122_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; uint64_t v___x_2104_; uint64_t v___x_2105_; uint64_t v___x_2106_; uint64_t v_fold_2107_; uint64_t v___x_2108_; uint64_t v___x_2109_; uint64_t v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; size_t v___x_2114_; size_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2103_ = lean_array_get_size(v_x_2095_);
v___x_2104_ = l_Lean_Expr_hash(v_key_2097_);
v___x_2105_ = 32ULL;
v___x_2106_ = lean_uint64_shift_right(v___x_2104_, v___x_2105_);
v_fold_2107_ = lean_uint64_xor(v___x_2104_, v___x_2106_);
v___x_2108_ = 16ULL;
v___x_2109_ = lean_uint64_shift_right(v_fold_2107_, v___x_2108_);
v___x_2110_ = lean_uint64_xor(v_fold_2107_, v___x_2109_);
v___x_2111_ = lean_uint64_to_usize(v___x_2110_);
v___x_2112_ = lean_usize_of_nat(v___x_2103_);
v___x_2113_ = ((size_t)1ULL);
v___x_2114_ = lean_usize_sub(v___x_2112_, v___x_2113_);
v___x_2115_ = lean_usize_land(v___x_2111_, v___x_2114_);
v___x_2116_ = lean_array_uget_borrowed(v_x_2095_, v___x_2115_);
lean_inc(v___x_2116_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 2, v___x_2116_);
v___x_2118_ = v___x_2101_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_key_2097_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_value_2098_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_array_uset(v_x_2095_, v___x_2115_, v___x_2118_);
v_x_2095_ = v___x_2119_;
v_x_2096_ = v_tail_2099_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(lean_object* v_i_2123_, lean_object* v_source_2124_, lean_object* v_target_2125_){
_start:
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = lean_array_get_size(v_source_2124_);
v___x_2127_ = lean_nat_dec_lt(v_i_2123_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_dec_ref(v_source_2124_);
lean_dec(v_i_2123_);
return v_target_2125_;
}
else
{
lean_object* v_es_2128_; lean_object* v___x_2129_; lean_object* v_source_2130_; lean_object* v_target_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_es_2128_ = lean_array_fget(v_source_2124_, v_i_2123_);
v___x_2129_ = lean_box(0);
v_source_2130_ = lean_array_fset(v_source_2124_, v_i_2123_, v___x_2129_);
v_target_2131_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_target_2125_, v_es_2128_);
v___x_2132_ = lean_unsigned_to_nat(1u);
v___x_2133_ = lean_nat_add(v_i_2123_, v___x_2132_);
lean_dec(v_i_2123_);
v_i_2123_ = v___x_2133_;
v_source_2124_ = v_source_2130_;
v_target_2125_ = v_target_2131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(lean_object* v_data_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v_nbuckets_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2136_ = lean_array_get_size(v_data_2135_);
v___x_2137_ = lean_unsigned_to_nat(2u);
v_nbuckets_2138_ = lean_nat_mul(v___x_2136_, v___x_2137_);
v___x_2139_ = lean_unsigned_to_nat(0u);
v___x_2140_ = lean_box(0);
v___x_2141_ = lean_mk_array(v_nbuckets_2138_, v___x_2140_);
v___x_2142_ = lean_array_propagate_mark(v_data_2135_, v___x_2141_);
v___x_2143_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v___x_2139_, v_data_2135_, v___x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(lean_object* v_a_2144_, lean_object* v_x_2145_){
_start:
{
if (lean_obj_tag(v_x_2145_) == 0)
{
uint8_t v___x_2146_; 
v___x_2146_ = 0;
return v___x_2146_;
}
else
{
lean_object* v_key_2147_; lean_object* v_tail_2148_; uint8_t v___x_2149_; 
v_key_2147_ = lean_ctor_get(v_x_2145_, 0);
v_tail_2148_ = lean_ctor_get(v_x_2145_, 2);
v___x_2149_ = lean_expr_eqv(v_key_2147_, v_a_2144_);
if (v___x_2149_ == 0)
{
v_x_2145_ = v_tail_2148_;
goto _start;
}
else
{
return v___x_2149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg___boxed(lean_object* v_a_2151_, lean_object* v_x_2152_){
_start:
{
uint8_t v_res_2153_; lean_object* v_r_2154_; 
v_res_2153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2151_, v_x_2152_);
lean_dec(v_x_2152_);
lean_dec_ref(v_a_2151_);
v_r_2154_ = lean_box(v_res_2153_);
return v_r_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(lean_object* v_m_2155_, lean_object* v_a_2156_, lean_object* v_b_2157_){
_start:
{
lean_object* v_size_2158_; lean_object* v_buckets_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2202_; 
v_size_2158_ = lean_ctor_get(v_m_2155_, 0);
v_buckets_2159_ = lean_ctor_get(v_m_2155_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_m_2155_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2161_ = v_m_2155_;
v_isShared_2162_ = v_isSharedCheck_2202_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_buckets_2159_);
lean_inc(v_size_2158_);
lean_dec(v_m_2155_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2202_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; uint64_t v___x_2164_; uint64_t v___x_2165_; uint64_t v___x_2166_; uint64_t v_fold_2167_; uint64_t v___x_2168_; uint64_t v___x_2169_; uint64_t v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; size_t v___x_2173_; size_t v___x_2174_; size_t v___x_2175_; lean_object* v_bkt_2176_; uint8_t v___x_2177_; 
v___x_2163_ = lean_array_get_size(v_buckets_2159_);
v___x_2164_ = l_Lean_Expr_hash(v_a_2156_);
v___x_2165_ = 32ULL;
v___x_2166_ = lean_uint64_shift_right(v___x_2164_, v___x_2165_);
v_fold_2167_ = lean_uint64_xor(v___x_2164_, v___x_2166_);
v___x_2168_ = 16ULL;
v___x_2169_ = lean_uint64_shift_right(v_fold_2167_, v___x_2168_);
v___x_2170_ = lean_uint64_xor(v_fold_2167_, v___x_2169_);
v___x_2171_ = lean_uint64_to_usize(v___x_2170_);
v___x_2172_ = lean_usize_of_nat(v___x_2163_);
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = lean_usize_sub(v___x_2172_, v___x_2173_);
v___x_2175_ = lean_usize_land(v___x_2171_, v___x_2174_);
v_bkt_2176_ = lean_array_uget_borrowed(v_buckets_2159_, v___x_2175_);
v___x_2177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2156_, v_bkt_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v_size_x27_2179_; lean_object* v___x_2180_; lean_object* v_buckets_x27_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v_size_x27_2179_ = lean_nat_add(v_size_2158_, v___x_2178_);
lean_dec(v_size_2158_);
lean_inc(v_bkt_2176_);
v___x_2180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2180_, 0, v_a_2156_);
lean_ctor_set(v___x_2180_, 1, v_b_2157_);
lean_ctor_set(v___x_2180_, 2, v_bkt_2176_);
v_buckets_x27_2181_ = lean_array_uset(v_buckets_2159_, v___x_2175_, v___x_2180_);
v___x_2182_ = lean_unsigned_to_nat(4u);
v___x_2183_ = lean_nat_mul(v_size_x27_2179_, v___x_2182_);
v___x_2184_ = lean_unsigned_to_nat(3u);
v___x_2185_ = lean_nat_div(v___x_2183_, v___x_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_array_get_size(v_buckets_x27_2181_);
v___x_2187_ = lean_nat_dec_le(v___x_2185_, v___x_2186_);
lean_dec(v___x_2185_);
if (v___x_2187_ == 0)
{
lean_object* v_val_2188_; lean_object* v___x_2190_; 
v_val_2188_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_buckets_x27_2181_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v_val_2188_);
lean_ctor_set(v___x_2161_, 0, v_size_x27_2179_);
v___x_2190_ = v___x_2161_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_size_x27_2179_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_val_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
else
{
lean_object* v___x_2193_; 
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v_buckets_x27_2181_);
lean_ctor_set(v___x_2161_, 0, v_size_x27_2179_);
v___x_2193_ = v___x_2161_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_size_x27_2179_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_buckets_x27_2181_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
else
{
lean_object* v___x_2195_; lean_object* v_buckets_x27_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
lean_inc(v_bkt_2176_);
v___x_2195_ = lean_box(0);
v_buckets_x27_2196_ = lean_array_uset(v_buckets_2159_, v___x_2175_, v___x_2195_);
v___x_2197_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2156_, v_b_2157_, v_bkt_2176_);
v___x_2198_ = lean_array_uset(v_buckets_x27_2196_, v___x_2175_, v___x_2197_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v___x_2198_);
v___x_2200_ = v___x_2161_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_size_2158_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(lean_object* v_a_2203_, lean_object* v_x_2204_){
_start:
{
if (lean_obj_tag(v_x_2204_) == 0)
{
lean_object* v___x_2205_; 
v___x_2205_ = lean_box(0);
return v___x_2205_;
}
else
{
lean_object* v_key_2206_; lean_object* v_value_2207_; lean_object* v_tail_2208_; uint8_t v___x_2209_; 
v_key_2206_ = lean_ctor_get(v_x_2204_, 0);
v_value_2207_ = lean_ctor_get(v_x_2204_, 1);
v_tail_2208_ = lean_ctor_get(v_x_2204_, 2);
v___x_2209_ = lean_expr_eqv(v_key_2206_, v_a_2203_);
if (v___x_2209_ == 0)
{
v_x_2204_ = v_tail_2208_;
goto _start;
}
else
{
lean_object* v___x_2211_; 
lean_inc(v_value_2207_);
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_value_2207_);
return v___x_2211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg___boxed(lean_object* v_a_2212_, lean_object* v_x_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2212_, v_x_2213_);
lean_dec(v_x_2213_);
lean_dec_ref(v_a_2212_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(lean_object* v_m_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v_buckets_2217_; lean_object* v___x_2218_; uint64_t v___x_2219_; uint64_t v___x_2220_; uint64_t v___x_2221_; uint64_t v_fold_2222_; uint64_t v___x_2223_; uint64_t v___x_2224_; uint64_t v___x_2225_; size_t v___x_2226_; size_t v___x_2227_; size_t v___x_2228_; size_t v___x_2229_; size_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_buckets_2217_ = lean_ctor_get(v_m_2215_, 1);
v___x_2218_ = lean_array_get_size(v_buckets_2217_);
v___x_2219_ = l_Lean_Expr_hash(v_a_2216_);
v___x_2220_ = 32ULL;
v___x_2221_ = lean_uint64_shift_right(v___x_2219_, v___x_2220_);
v_fold_2222_ = lean_uint64_xor(v___x_2219_, v___x_2221_);
v___x_2223_ = 16ULL;
v___x_2224_ = lean_uint64_shift_right(v_fold_2222_, v___x_2223_);
v___x_2225_ = lean_uint64_xor(v_fold_2222_, v___x_2224_);
v___x_2226_ = lean_uint64_to_usize(v___x_2225_);
v___x_2227_ = lean_usize_of_nat(v___x_2218_);
v___x_2228_ = ((size_t)1ULL);
v___x_2229_ = lean_usize_sub(v___x_2227_, v___x_2228_);
v___x_2230_ = lean_usize_land(v___x_2226_, v___x_2229_);
v___x_2231_ = lean_array_uget_borrowed(v_buckets_2217_, v___x_2230_);
v___x_2232_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2216_, v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg___boxed(lean_object* v_m_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2233_, v_a_2234_);
lean_dec_ref(v_a_2234_);
lean_dec_ref(v_m_2233_);
return v_res_2235_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2237_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_2238_ = lean_unsigned_to_nat(26u);
v___x_2239_ = lean_unsigned_to_nat(152u);
v___x_2240_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0));
v___x_2241_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2242_ = l_mkPanicMessageWithDecl(v___x_2241_, v___x_2240_, v___x_2239_, v___x_2238_, v___x_2237_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData(lean_object* v_e_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_e_x27_2248_; lean_object* v_visitedNames_2249_; lean_object* v_visitedLevels_2250_; lean_object* v_visitedExprs_2251_; lean_object* v_visitedConstants_2252_; lean_object* v_noMDataExprs_2253_; uint8_t v_exportMData_2254_; uint8_t v_exportUnsafe_2255_; uint8_t v_ignoreMissing_2256_; lean_object* v_recursorMap_2257_; lean_object* v_e_x27_2263_; lean_object* v___y_2264_; lean_object* v_visitedNames_2274_; lean_object* v_visitedLevels_2275_; lean_object* v_visitedExprs_2276_; lean_object* v_visitedConstants_2277_; lean_object* v_noMDataExprs_2278_; uint8_t v_exportMData_2279_; uint8_t v_exportUnsafe_2280_; uint8_t v_ignoreMissing_2281_; lean_object* v_recursorMap_2282_; lean_object* v___x_2283_; 
v_visitedNames_2274_ = lean_ctor_get(v_a_2245_, 0);
v_visitedLevels_2275_ = lean_ctor_get(v_a_2245_, 1);
v_visitedExprs_2276_ = lean_ctor_get(v_a_2245_, 2);
v_visitedConstants_2277_ = lean_ctor_get(v_a_2245_, 3);
v_noMDataExprs_2278_ = lean_ctor_get(v_a_2245_, 4);
v_exportMData_2279_ = lean_ctor_get_uint8(v_a_2245_, sizeof(void*)*6);
v_exportUnsafe_2280_ = lean_ctor_get_uint8(v_a_2245_, sizeof(void*)*6 + 1);
v_ignoreMissing_2281_ = lean_ctor_get_uint8(v_a_2245_, sizeof(void*)*6 + 2);
v_recursorMap_2282_ = lean_ctor_get(v_a_2245_, 5);
v___x_2283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_noMDataExprs_2278_, v_e_2243_);
if (lean_obj_tag(v___x_2283_) == 1)
{
lean_object* v_val_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref(v_e_2243_);
v_val_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_val_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v_val_2284_);
lean_ctor_set(v___x_2288_, 1, v_a_2245_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set_tag(v___x_2286_, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2288_);
v___x_2290_ = v___x_2286_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
else
{
lean_dec(v___x_2283_);
switch(lean_obj_tag(v_e_2243_))
{
case 1:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2294_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2293_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v_fst_2296_; lean_object* v_snd_2297_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v_fst_2296_ = lean_ctor_get(v_a_2295_, 0);
lean_inc(v_fst_2296_);
v_snd_2297_ = lean_ctor_get(v_a_2295_, 1);
lean_inc(v_snd_2297_);
lean_dec(v_a_2295_);
v_e_x27_2263_ = v_fst_2296_;
v___y_2264_ = v_snd_2297_;
goto v___jp_2262_;
}
else
{
lean_dec_ref_known(v_e_2243_, 1);
return v___x_2294_;
}
}
case 2:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2299_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2298_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v_fst_2301_; lean_object* v_snd_2302_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v_fst_2301_ = lean_ctor_get(v_a_2300_, 0);
lean_inc(v_fst_2301_);
v_snd_2302_ = lean_ctor_get(v_a_2300_, 1);
lean_inc(v_snd_2302_);
lean_dec(v_a_2300_);
v_e_x27_2263_ = v_fst_2301_;
v___y_2264_ = v_snd_2302_;
goto v___jp_2262_;
}
else
{
lean_dec_ref_known(v_e_2243_, 1);
return v___x_2299_;
}
}
case 5:
{
lean_object* v_fn_2303_; lean_object* v_arg_2304_; lean_object* v___x_2305_; 
v_fn_2303_ = lean_ctor_get(v_e_2243_, 0);
v_arg_2304_ = lean_ctor_get(v_e_2243_, 1);
lean_inc_ref(v_fn_2303_);
v___x_2305_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_fn_2303_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v_fst_2307_; lean_object* v_snd_2308_; lean_object* v___x_2309_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v_fst_2307_ = lean_ctor_get(v_a_2306_, 0);
lean_inc(v_fst_2307_);
v_snd_2308_ = lean_ctor_get(v_a_2306_, 1);
lean_inc(v_snd_2308_);
lean_dec(v_a_2306_);
lean_inc_ref(v_arg_2304_);
v___x_2309_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_arg_2304_, v_a_2244_, v_snd_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v_fst_2311_; lean_object* v_snd_2312_; size_t v___x_2313_; size_t v___x_2314_; uint8_t v___x_2315_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v_fst_2311_ = lean_ctor_get(v_a_2310_, 0);
lean_inc(v_fst_2311_);
v_snd_2312_ = lean_ctor_get(v_a_2310_, 1);
lean_inc(v_snd_2312_);
lean_dec(v_a_2310_);
v___x_2313_ = lean_ptr_addr(v_fn_2303_);
v___x_2314_ = lean_ptr_addr(v_fst_2307_);
v___x_2315_ = lean_usize_dec_eq(v___x_2313_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Expr_app___override(v_fst_2307_, v_fst_2311_);
v_e_x27_2263_ = v___x_2316_;
v___y_2264_ = v_snd_2312_;
goto v___jp_2262_;
}
else
{
size_t v___x_2317_; size_t v___x_2318_; uint8_t v___x_2319_; 
v___x_2317_ = lean_ptr_addr(v_arg_2304_);
v___x_2318_ = lean_ptr_addr(v_fst_2311_);
v___x_2319_ = lean_usize_dec_eq(v___x_2317_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_Expr_app___override(v_fst_2307_, v_fst_2311_);
v_e_x27_2263_ = v___x_2320_;
v___y_2264_ = v_snd_2312_;
goto v___jp_2262_;
}
else
{
lean_dec(v_fst_2311_);
lean_dec(v_fst_2307_);
lean_inc_ref(v_e_2243_);
v_e_x27_2263_ = v_e_2243_;
v___y_2264_ = v_snd_2312_;
goto v___jp_2262_;
}
}
}
else
{
lean_dec(v_fst_2307_);
lean_dec_ref_known(v_e_2243_, 2);
return v___x_2309_;
}
}
else
{
lean_dec_ref_known(v_e_2243_, 2);
return v___x_2305_;
}
}
case 6:
{
lean_object* v_binderName_2321_; lean_object* v_binderType_2322_; lean_object* v_body_2323_; uint8_t v_binderInfo_2324_; lean_object* v___x_2325_; 
v_binderName_2321_ = lean_ctor_get(v_e_2243_, 0);
v_binderType_2322_ = lean_ctor_get(v_e_2243_, 1);
v_body_2323_ = lean_ctor_get(v_e_2243_, 2);
v_binderInfo_2324_ = lean_ctor_get_uint8(v_e_2243_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2322_);
v___x_2325_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2322_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v_fst_2327_; lean_object* v_snd_2328_; lean_object* v___x_2329_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v_fst_2327_ = lean_ctor_get(v_a_2326_, 0);
lean_inc(v_fst_2327_);
v_snd_2328_ = lean_ctor_get(v_a_2326_, 1);
lean_inc(v_snd_2328_);
lean_dec(v_a_2326_);
lean_inc_ref(v_body_2323_);
v___x_2329_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2323_, v_a_2244_, v_snd_2328_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v_fst_2331_; lean_object* v_snd_2332_; size_t v___x_2333_; size_t v___x_2334_; uint8_t v___x_2335_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v_fst_2331_ = lean_ctor_get(v_a_2330_, 0);
lean_inc(v_fst_2331_);
v_snd_2332_ = lean_ctor_get(v_a_2330_, 1);
lean_inc(v_snd_2332_);
lean_dec(v_a_2330_);
v___x_2333_ = lean_ptr_addr(v_binderType_2322_);
v___x_2334_ = lean_ptr_addr(v_fst_2327_);
v___x_2335_ = lean_usize_dec_eq(v___x_2333_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; 
lean_inc(v_binderName_2321_);
v___x_2336_ = l_Lean_Expr_lam___override(v_binderName_2321_, v_fst_2327_, v_fst_2331_, v_binderInfo_2324_);
v_e_x27_2263_ = v___x_2336_;
v___y_2264_ = v_snd_2332_;
goto v___jp_2262_;
}
else
{
size_t v___x_2337_; size_t v___x_2338_; uint8_t v___x_2339_; 
v___x_2337_ = lean_ptr_addr(v_body_2323_);
v___x_2338_ = lean_ptr_addr(v_fst_2331_);
v___x_2339_ = lean_usize_dec_eq(v___x_2337_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; 
lean_inc(v_binderName_2321_);
v___x_2340_ = l_Lean_Expr_lam___override(v_binderName_2321_, v_fst_2327_, v_fst_2331_, v_binderInfo_2324_);
v_e_x27_2263_ = v___x_2340_;
v___y_2264_ = v_snd_2332_;
goto v___jp_2262_;
}
else
{
uint8_t v___x_2341_; 
v___x_2341_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2324_, v_binderInfo_2324_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
lean_inc(v_binderName_2321_);
v___x_2342_ = l_Lean_Expr_lam___override(v_binderName_2321_, v_fst_2327_, v_fst_2331_, v_binderInfo_2324_);
v_e_x27_2263_ = v___x_2342_;
v___y_2264_ = v_snd_2332_;
goto v___jp_2262_;
}
else
{
lean_dec(v_fst_2331_);
lean_dec(v_fst_2327_);
lean_inc_ref(v_e_2243_);
v_e_x27_2263_ = v_e_2243_;
v___y_2264_ = v_snd_2332_;
goto v___jp_2262_;
}
}
}
}
else
{
lean_dec(v_fst_2327_);
lean_dec_ref_known(v_e_2243_, 3);
return v___x_2329_;
}
}
else
{
lean_dec_ref_known(v_e_2243_, 3);
return v___x_2325_;
}
}
case 7:
{
lean_object* v_binderName_2343_; lean_object* v_binderType_2344_; lean_object* v_body_2345_; uint8_t v_binderInfo_2346_; lean_object* v___x_2347_; 
v_binderName_2343_ = lean_ctor_get(v_e_2243_, 0);
v_binderType_2344_ = lean_ctor_get(v_e_2243_, 1);
v_body_2345_ = lean_ctor_get(v_e_2243_, 2);
v_binderInfo_2346_ = lean_ctor_get_uint8(v_e_2243_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2344_);
v___x_2347_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2344_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v_fst_2349_; lean_object* v_snd_2350_; lean_object* v___x_2351_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v_fst_2349_ = lean_ctor_get(v_a_2348_, 0);
lean_inc(v_fst_2349_);
v_snd_2350_ = lean_ctor_get(v_a_2348_, 1);
lean_inc(v_snd_2350_);
lean_dec(v_a_2348_);
lean_inc_ref(v_body_2345_);
v___x_2351_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2345_, v_a_2244_, v_snd_2350_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v_fst_2353_; lean_object* v_snd_2354_; size_t v___x_2355_; size_t v___x_2356_; uint8_t v___x_2357_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v_fst_2353_ = lean_ctor_get(v_a_2352_, 0);
lean_inc(v_fst_2353_);
v_snd_2354_ = lean_ctor_get(v_a_2352_, 1);
lean_inc(v_snd_2354_);
lean_dec(v_a_2352_);
v___x_2355_ = lean_ptr_addr(v_binderType_2344_);
v___x_2356_ = lean_ptr_addr(v_fst_2349_);
v___x_2357_ = lean_usize_dec_eq(v___x_2355_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
lean_inc(v_binderName_2343_);
v___x_2358_ = l_Lean_Expr_forallE___override(v_binderName_2343_, v_fst_2349_, v_fst_2353_, v_binderInfo_2346_);
v_e_x27_2263_ = v___x_2358_;
v___y_2264_ = v_snd_2354_;
goto v___jp_2262_;
}
else
{
size_t v___x_2359_; size_t v___x_2360_; uint8_t v___x_2361_; 
v___x_2359_ = lean_ptr_addr(v_body_2345_);
v___x_2360_ = lean_ptr_addr(v_fst_2353_);
v___x_2361_ = lean_usize_dec_eq(v___x_2359_, v___x_2360_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; 
lean_inc(v_binderName_2343_);
v___x_2362_ = l_Lean_Expr_forallE___override(v_binderName_2343_, v_fst_2349_, v_fst_2353_, v_binderInfo_2346_);
v_e_x27_2263_ = v___x_2362_;
v___y_2264_ = v_snd_2354_;
goto v___jp_2262_;
}
else
{
uint8_t v___x_2363_; 
v___x_2363_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2346_, v_binderInfo_2346_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; 
lean_inc(v_binderName_2343_);
v___x_2364_ = l_Lean_Expr_forallE___override(v_binderName_2343_, v_fst_2349_, v_fst_2353_, v_binderInfo_2346_);
v_e_x27_2263_ = v___x_2364_;
v___y_2264_ = v_snd_2354_;
goto v___jp_2262_;
}
else
{
lean_dec(v_fst_2353_);
lean_dec(v_fst_2349_);
lean_inc_ref(v_e_2243_);
v_e_x27_2263_ = v_e_2243_;
v___y_2264_ = v_snd_2354_;
goto v___jp_2262_;
}
}
}
}
else
{
lean_dec(v_fst_2349_);
lean_dec_ref_known(v_e_2243_, 3);
return v___x_2351_;
}
}
else
{
lean_dec_ref_known(v_e_2243_, 3);
return v___x_2347_;
}
}
case 8:
{
lean_object* v_declName_2365_; lean_object* v_type_2366_; lean_object* v_value_2367_; lean_object* v_body_2368_; uint8_t v_nondep_2369_; lean_object* v___x_2370_; 
v_declName_2365_ = lean_ctor_get(v_e_2243_, 0);
v_type_2366_ = lean_ctor_get(v_e_2243_, 1);
v_value_2367_ = lean_ctor_get(v_e_2243_, 2);
v_body_2368_ = lean_ctor_get(v_e_2243_, 3);
v_nondep_2369_ = lean_ctor_get_uint8(v_e_2243_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2366_);
v___x_2370_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_type_2366_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v_fst_2372_; lean_object* v_snd_2373_; lean_object* v___x_2374_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v_fst_2372_ = lean_ctor_get(v_a_2371_, 0);
lean_inc(v_fst_2372_);
v_snd_2373_ = lean_ctor_get(v_a_2371_, 1);
lean_inc(v_snd_2373_);
lean_dec(v_a_2371_);
lean_inc_ref(v_value_2367_);
v___x_2374_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_value_2367_, v_a_2244_, v_snd_2373_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v_fst_2376_; lean_object* v_snd_2377_; lean_object* v___x_2378_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v_fst_2376_ = lean_ctor_get(v_a_2375_, 0);
lean_inc(v_fst_2376_);
v_snd_2377_ = lean_ctor_get(v_a_2375_, 1);
lean_inc(v_snd_2377_);
lean_dec(v_a_2375_);
lean_inc_ref(v_body_2368_);
v___x_2378_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2368_, v_a_2244_, v_snd_2377_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v_fst_2380_; lean_object* v_snd_2381_; uint8_t v___x_2382_; size_t v___x_2383_; size_t v___x_2384_; uint8_t v___x_2385_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v_fst_2380_ = lean_ctor_get(v_a_2379_, 0);
lean_inc(v_fst_2380_);
v_snd_2381_ = lean_ctor_get(v_a_2379_, 1);
lean_inc(v_snd_2381_);
lean_dec(v_a_2379_);
v___x_2382_ = 0;
v___x_2383_ = lean_ptr_addr(v_type_2366_);
v___x_2384_ = lean_ptr_addr(v_fst_2372_);
v___x_2385_ = lean_usize_dec_eq(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; 
lean_inc(v_declName_2365_);
v___x_2386_ = l_Lean_Expr_letE___override(v_declName_2365_, v_fst_2372_, v_fst_2376_, v_fst_2380_, v___x_2382_);
v_e_x27_2263_ = v___x_2386_;
v___y_2264_ = v_snd_2381_;
goto v___jp_2262_;
}
else
{
size_t v___x_2387_; size_t v___x_2388_; uint8_t v___x_2389_; 
v___x_2387_ = lean_ptr_addr(v_value_2367_);
v___x_2388_ = lean_ptr_addr(v_fst_2376_);
v___x_2389_ = lean_usize_dec_eq(v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; 
lean_inc(v_declName_2365_);
v___x_2390_ = l_Lean_Expr_letE___override(v_declName_2365_, v_fst_2372_, v_fst_2376_, v_fst_2380_, v___x_2382_);
v_e_x27_2263_ = v___x_2390_;
v___y_2264_ = v_snd_2381_;
goto v___jp_2262_;
}
else
{
size_t v___x_2391_; size_t v___x_2392_; uint8_t v___x_2393_; 
v___x_2391_ = lean_ptr_addr(v_body_2368_);
v___x_2392_ = lean_ptr_addr(v_fst_2380_);
v___x_2393_ = lean_usize_dec_eq(v___x_2391_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; 
lean_inc(v_declName_2365_);
v___x_2394_ = l_Lean_Expr_letE___override(v_declName_2365_, v_fst_2372_, v_fst_2376_, v_fst_2380_, v___x_2382_);
v_e_x27_2263_ = v___x_2394_;
v___y_2264_ = v_snd_2381_;
goto v___jp_2262_;
}
else
{
if (v_nondep_2369_ == 0)
{
lean_dec(v_fst_2380_);
lean_dec(v_fst_2376_);
lean_dec(v_fst_2372_);
lean_inc_ref(v_e_2243_);
v_e_x27_2263_ = v_e_2243_;
v___y_2264_ = v_snd_2381_;
goto v___jp_2262_;
}
else
{
lean_object* v___x_2395_; 
lean_inc(v_declName_2365_);
v___x_2395_ = l_Lean_Expr_letE___override(v_declName_2365_, v_fst_2372_, v_fst_2376_, v_fst_2380_, v___x_2382_);
v_e_x27_2263_ = v___x_2395_;
v___y_2264_ = v_snd_2381_;
goto v___jp_2262_;
}
}
}
}
}
else
{
lean_dec(v_fst_2376_);
lean_dec(v_fst_2372_);
lean_dec_ref_known(v_e_2243_, 4);
return v___x_2378_;
}
}
else
{
lean_dec(v_fst_2372_);
lean_dec_ref_known(v_e_2243_, 4);
return v___x_2374_;
}
}
else
{
lean_dec_ref_known(v_e_2243_, 4);
return v___x_2370_;
}
}
case 10:
{
lean_object* v_expr_2396_; lean_object* v___x_2397_; 
v_expr_2396_ = lean_ctor_get(v_e_2243_, 1);
lean_inc_ref(v_expr_2396_);
v___x_2397_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_expr_2396_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v_fst_2399_; lean_object* v_snd_2400_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2397_, 1);
v_fst_2399_ = lean_ctor_get(v_a_2398_, 0);
lean_inc(v_fst_2399_);
v_snd_2400_ = lean_ctor_get(v_a_2398_, 1);
lean_inc(v_snd_2400_);
lean_dec(v_a_2398_);
v_e_x27_2263_ = v_fst_2399_;
v___y_2264_ = v_snd_2400_;
goto v___jp_2262_;
}
else
{
lean_dec_ref_known(v_e_2243_, 2);
return v___x_2397_;
}
}
case 11:
{
lean_object* v_typeName_2401_; lean_object* v_idx_2402_; lean_object* v_struct_2403_; lean_object* v___x_2404_; 
v_typeName_2401_ = lean_ctor_get(v_e_2243_, 0);
v_idx_2402_ = lean_ctor_get(v_e_2243_, 1);
v_struct_2403_ = lean_ctor_get(v_e_2243_, 2);
lean_inc_ref(v_struct_2403_);
v___x_2404_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_struct_2403_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v_fst_2406_; lean_object* v_snd_2407_; size_t v___x_2408_; size_t v___x_2409_; uint8_t v___x_2410_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v_fst_2406_ = lean_ctor_get(v_a_2405_, 0);
lean_inc(v_fst_2406_);
v_snd_2407_ = lean_ctor_get(v_a_2405_, 1);
lean_inc(v_snd_2407_);
lean_dec(v_a_2405_);
v___x_2408_ = lean_ptr_addr(v_struct_2403_);
v___x_2409_ = lean_ptr_addr(v_fst_2406_);
v___x_2410_ = lean_usize_dec_eq(v___x_2408_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; 
lean_inc(v_idx_2402_);
lean_inc(v_typeName_2401_);
v___x_2411_ = l_Lean_Expr_proj___override(v_typeName_2401_, v_idx_2402_, v_fst_2406_);
v_e_x27_2263_ = v___x_2411_;
v___y_2264_ = v_snd_2407_;
goto v___jp_2262_;
}
else
{
lean_dec(v_fst_2406_);
lean_inc_ref(v_e_2243_);
v_e_x27_2263_ = v_e_2243_;
v___y_2264_ = v_snd_2407_;
goto v___jp_2262_;
}
}
else
{
lean_dec_ref_known(v_e_2243_, 3);
return v___x_2404_;
}
}
default: 
{
lean_inc(v_recursorMap_2282_);
lean_inc_ref(v_noMDataExprs_2278_);
lean_inc_ref(v_visitedConstants_2277_);
lean_inc_ref(v_visitedExprs_2276_);
lean_inc_ref(v_visitedLevels_2275_);
lean_inc_ref(v_visitedNames_2274_);
lean_dec_ref(v_a_2245_);
lean_inc_ref(v_e_2243_);
v_e_x27_2248_ = v_e_2243_;
v_visitedNames_2249_ = v_visitedNames_2274_;
v_visitedLevels_2250_ = v_visitedLevels_2275_;
v_visitedExprs_2251_ = v_visitedExprs_2276_;
v_visitedConstants_2252_ = v_visitedConstants_2277_;
v_noMDataExprs_2253_ = v_noMDataExprs_2278_;
v_exportMData_2254_ = v_exportMData_2279_;
v_exportUnsafe_2255_ = v_exportUnsafe_2280_;
v_ignoreMissing_2256_ = v_ignoreMissing_2281_;
v_recursorMap_2257_ = v_recursorMap_2282_;
goto v___jp_2247_;
}
}
}
v___jp_2247_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_inc_ref(v_e_x27_2248_);
v___x_2258_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_noMDataExprs_2253_, v_e_2243_, v_e_x27_2248_);
v___x_2259_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_2259_, 0, v_visitedNames_2249_);
lean_ctor_set(v___x_2259_, 1, v_visitedLevels_2250_);
lean_ctor_set(v___x_2259_, 2, v_visitedExprs_2251_);
lean_ctor_set(v___x_2259_, 3, v_visitedConstants_2252_);
lean_ctor_set(v___x_2259_, 4, v___x_2258_);
lean_ctor_set(v___x_2259_, 5, v_recursorMap_2257_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*6, v_exportMData_2254_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*6 + 1, v_exportUnsafe_2255_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*6 + 2, v_ignoreMissing_2256_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v_e_x27_2248_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
return v___x_2261_;
}
v___jp_2262_:
{
lean_object* v_visitedNames_2265_; lean_object* v_visitedLevels_2266_; lean_object* v_visitedExprs_2267_; lean_object* v_visitedConstants_2268_; lean_object* v_noMDataExprs_2269_; uint8_t v_exportMData_2270_; uint8_t v_exportUnsafe_2271_; uint8_t v_ignoreMissing_2272_; lean_object* v_recursorMap_2273_; 
v_visitedNames_2265_ = lean_ctor_get(v___y_2264_, 0);
lean_inc_ref(v_visitedNames_2265_);
v_visitedLevels_2266_ = lean_ctor_get(v___y_2264_, 1);
lean_inc_ref(v_visitedLevels_2266_);
v_visitedExprs_2267_ = lean_ctor_get(v___y_2264_, 2);
lean_inc_ref(v_visitedExprs_2267_);
v_visitedConstants_2268_ = lean_ctor_get(v___y_2264_, 3);
lean_inc_ref(v_visitedConstants_2268_);
v_noMDataExprs_2269_ = lean_ctor_get(v___y_2264_, 4);
lean_inc_ref(v_noMDataExprs_2269_);
v_exportMData_2270_ = lean_ctor_get_uint8(v___y_2264_, sizeof(void*)*6);
v_exportUnsafe_2271_ = lean_ctor_get_uint8(v___y_2264_, sizeof(void*)*6 + 1);
v_ignoreMissing_2272_ = lean_ctor_get_uint8(v___y_2264_, sizeof(void*)*6 + 2);
v_recursorMap_2273_ = lean_ctor_get(v___y_2264_, 5);
lean_inc(v_recursorMap_2273_);
lean_dec_ref(v___y_2264_);
v_e_x27_2248_ = v_e_x27_2263_;
v_visitedNames_2249_ = v_visitedNames_2265_;
v_visitedLevels_2250_ = v_visitedLevels_2266_;
v_visitedExprs_2251_ = v_visitedExprs_2267_;
v_visitedConstants_2252_ = v_visitedConstants_2268_;
v_noMDataExprs_2253_ = v_noMDataExprs_2269_;
v_exportMData_2254_ = v_exportMData_2270_;
v_exportUnsafe_2255_ = v_exportUnsafe_2271_;
v_ignoreMissing_2256_ = v_ignoreMissing_2272_;
v_recursorMap_2257_ = v_recursorMap_2273_;
goto v___jp_2247_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___boxed(lean_object* v_e_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_2412_, v_a_2413_, v_a_2414_);
lean_dec_ref(v_a_2413_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0(lean_object* v_00_u03b2_2417_, lean_object* v_m_2418_, lean_object* v_a_2419_, lean_object* v_b_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_m_2418_, v_a_2419_, v_b_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(lean_object* v_00_u03b2_2422_, lean_object* v_m_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2423_, v_a_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___boxed(lean_object* v_00_u03b2_2426_, lean_object* v_m_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(v_00_u03b2_2426_, v_m_2427_, v_a_2428_);
lean_dec_ref(v_a_2428_);
lean_dec_ref(v_m_2427_);
return v_res_2429_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(lean_object* v_00_u03b2_2430_, lean_object* v_a_2431_, lean_object* v_x_2432_){
_start:
{
uint8_t v___x_2433_; 
v___x_2433_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2431_, v_x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2434_, lean_object* v_a_2435_, lean_object* v_x_2436_){
_start:
{
uint8_t v_res_2437_; lean_object* v_r_2438_; 
v_res_2437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(v_00_u03b2_2434_, v_a_2435_, v_x_2436_);
lean_dec(v_x_2436_);
lean_dec_ref(v_a_2435_);
v_r_2438_ = lean_box(v_res_2437_);
return v_r_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1(lean_object* v_00_u03b2_2439_, lean_object* v_data_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_data_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2(lean_object* v_00_u03b2_2442_, lean_object* v_a_2443_, lean_object* v_b_2444_, lean_object* v_x_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2443_, v_b_2444_, v_x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(lean_object* v_00_u03b2_2447_, lean_object* v_a_2448_, lean_object* v_x_2449_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2448_, v_x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2451_, lean_object* v_a_2452_, lean_object* v_x_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(v_00_u03b2_2451_, v_a_2452_, v_x_2453_);
lean_dec(v_x_2453_);
lean_dec_ref(v_a_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2455_, lean_object* v_i_2456_, lean_object* v_source_2457_, lean_object* v_target_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v_i_2456_, v_source_2457_, v_target_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2460_, lean_object* v_x_2461_, lean_object* v_x_2462_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_x_2461_, v_x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(lean_object* v_fields_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = l_Lean_Json_mkObj(v_fields_2464_);
v___x_2468_ = l_Lean_Json_compress(v___x_2467_);
v___x_2469_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_2468_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2478_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2472_ = v___x_2469_;
v_isShared_2473_ = v_isSharedCheck_2478_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2469_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2478_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_a_2470_);
lean_ctor_set(v___x_2474_, 1, v_a_2465_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2474_);
v___x_2476_ = v___x_2472_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v_a_2465_);
v_a_2479_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2469_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2469_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg___boxed(lean_object* v_fields_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2487_, v_a_2488_);
lean_dec(v_fields_2487_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(lean_object* v_fields_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2491_, v_a_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___boxed(lean_object* v_fields_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(v_fields_2496_, v_a_2497_, v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_fields_2496_);
return v_res_2500_;
}
}
static lean_object* _init_l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Array_instInhabited(lean_box(0));
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object* v_msg_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v___x_2506_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___f_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___f_2520_; lean_object* v___x_162743__overap_2521_; lean_object* v___x_2522_; 
v___x_2506_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2507_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2507_, 0, v___x_2506_);
v___f_2508_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2508_, 0, v___x_2506_);
v___f_2509_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2509_, 0, v___x_2506_);
v___f_2510_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2510_, 0, v___x_2506_);
v___x_2511_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2511_, 0, lean_box(0));
lean_closure_set(v___x_2511_, 1, lean_box(0));
lean_closure_set(v___x_2511_, 2, v___x_2506_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v___f_2507_);
v___x_2513_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2513_, 0, lean_box(0));
lean_closure_set(v___x_2513_, 1, lean_box(0));
lean_closure_set(v___x_2513_, 2, v___x_2506_);
v___x_2514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
lean_ctor_set(v___x_2514_, 2, v___f_2508_);
lean_ctor_set(v___x_2514_, 3, v___f_2509_);
lean_ctor_set(v___x_2514_, 4, v___f_2510_);
v___x_2515_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2515_, 0, lean_box(0));
lean_closure_set(v___x_2515_, 1, lean_box(0));
lean_closure_set(v___x_2515_, 2, v___x_2506_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0);
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
v___x_2519_ = l_instInhabitedOfMonad___redArg(v___x_2516_, v___x_2518_);
v___f_2520_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2520_, 0, v___x_2519_);
v___x_162743__overap_2521_ = lean_panic_fn_borrowed(v___f_2520_, v_msg_2502_);
lean_dec_ref(v___f_2520_);
lean_inc_ref(v___y_2503_);
v___x_2522_ = lean_apply_3(v___x_162743__overap_2521_, v___y_2503_, v___y_2504_, lean_box(0));
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object* v_msg_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v_msg_2523_, v___y_2524_, v___y_2525_);
lean_dec_ref(v___y_2524_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object* v_msg_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___x_2532_; lean_object* v___f_2533_; lean_object* v___f_2534_; lean_object* v___f_2535_; lean_object* v___f_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___f_2545_; lean_object* v___x_162755__overap_2546_; lean_object* v___x_2547_; 
v___x_2532_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2533_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2533_, 0, v___x_2532_);
v___f_2534_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2534_, 0, v___x_2532_);
v___f_2535_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2535_, 0, v___x_2532_);
v___f_2536_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2536_, 0, v___x_2532_);
v___x_2537_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2537_, 0, lean_box(0));
lean_closure_set(v___x_2537_, 1, lean_box(0));
lean_closure_set(v___x_2537_, 2, v___x_2532_);
v___x_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
lean_ctor_set(v___x_2538_, 1, v___f_2533_);
v___x_2539_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2539_, 0, lean_box(0));
lean_closure_set(v___x_2539_, 1, lean_box(0));
lean_closure_set(v___x_2539_, 2, v___x_2532_);
v___x_2540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
lean_ctor_set(v___x_2540_, 2, v___f_2534_);
lean_ctor_set(v___x_2540_, 3, v___f_2535_);
lean_ctor_set(v___x_2540_, 4, v___f_2536_);
v___x_2541_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2541_, 0, lean_box(0));
lean_closure_set(v___x_2541_, 1, lean_box(0));
lean_closure_set(v___x_2541_, 2, v___x_2532_);
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_box(0);
v___x_2544_ = l_instInhabitedOfMonad___redArg(v___x_2542_, v___x_2543_);
v___f_2545_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2545_, 0, v___x_2544_);
v___x_162755__overap_2546_ = lean_panic_fn_borrowed(v___f_2545_, v_msg_2528_);
lean_dec_ref(v___f_2545_);
lean_inc_ref(v___y_2529_);
v___x_2547_ = lean_apply_3(v___x_162755__overap_2546_, v___y_2529_, v___y_2530_, lean_box(0));
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object* v_msg_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v_msg_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref(v___y_2549_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object* v_msg_2553_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = l_Lean_instInhabitedConstantInfo_default;
v___x_2555_ = lean_panic_fn_borrowed(v___x_2554_, v_msg_2553_);
return v___x_2555_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2558_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__1));
v___x_2559_ = lean_unsigned_to_nat(8u);
v___x_2560_ = lean_unsigned_to_nat(354u);
v___x_2561_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_2562_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2563_ = l_mkPanicMessageWithDecl(v___x_2562_, v___x_2561_, v___x_2560_, v___x_2559_, v___x_2558_);
return v___x_2563_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2565_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__3));
v___x_2566_ = lean_unsigned_to_nat(13u);
v___x_2567_ = lean_unsigned_to_nat(356u);
v___x_2568_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_2569_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2570_ = l_mkPanicMessageWithDecl(v___x_2569_, v___x_2568_, v___x_2567_, v___x_2566_, v___x_2565_);
return v___x_2570_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8(void){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2574_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__7));
v___x_2575_ = lean_unsigned_to_nat(14u);
v___x_2576_ = lean_unsigned_to_nat(22u);
v___x_2577_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__6));
v___x_2578_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__5));
v___x_2579_ = l_mkPanicMessageWithDecl(v___x_2578_, v___x_2577_, v___x_2576_, v___x_2575_, v___x_2574_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15(uint8_t v___x_2580_, lean_object* v_init_2581_, lean_object* v_x_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_d_2587_; lean_object* v___y_2588_; 
if (lean_obj_tag(v_x_2582_) == 0)
{
lean_object* v_k_2592_; lean_object* v_l_2593_; lean_object* v_r_2594_; lean_object* v___x_2595_; 
v_k_2592_ = lean_ctor_get(v_x_2582_, 1);
lean_inc(v_k_2592_);
v_l_2593_ = lean_ctor_get(v_x_2582_, 3);
lean_inc(v_l_2593_);
v_r_2594_ = lean_ctor_get(v_x_2582_, 4);
lean_inc(v_r_2594_);
lean_dec_ref_known(v_x_2582_, 5);
v___x_2595_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15(v___x_2580_, v_init_2581_, v_l_2593_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v_fst_2597_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v_fst_2597_ = lean_ctor_get(v_a_2596_, 0);
lean_inc(v_fst_2597_);
if (lean_obj_tag(v_fst_2597_) == 0)
{
lean_object* v_snd_2598_; lean_object* v_a_2599_; 
lean_dec(v_r_2594_);
lean_dec(v_k_2592_);
v_snd_2598_ = lean_ctor_get(v_a_2596_, 1);
lean_inc(v_snd_2598_);
lean_dec(v_a_2596_);
v_a_2599_ = lean_ctor_get(v_fst_2597_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v_fst_2597_, 1);
v_d_2587_ = v_a_2599_;
v___y_2588_ = v_snd_2598_;
goto v___jp_2586_;
}
else
{
lean_object* v_snd_2600_; lean_object* v_a_2601_; lean_object* v___y_2603_; lean_object* v___y_2607_; lean_object* v___x_2633_; 
v_snd_2600_ = lean_ctor_get(v_a_2596_, 1);
lean_inc(v_snd_2600_);
lean_dec(v_a_2596_);
v_a_2601_ = lean_ctor_get(v_fst_2597_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v_fst_2597_, 1);
lean_inc_ref(v___y_2583_);
v___x_2633_ = l_Lean_Environment_find_x3f(v___y_2583_, v_k_2592_, v___x_2580_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8);
v___x_2635_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2634_);
v___y_2607_ = v___x_2635_;
goto v___jp_2606_;
}
else
{
lean_object* v_val_2636_; 
v_val_2636_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_val_2636_);
lean_dec_ref_known(v___x_2633_, 1);
v___y_2607_ = v_val_2636_;
goto v___jp_2606_;
}
v___jp_2602_:
{
lean_object* v___x_2604_; 
v___x_2604_ = lean_array_push(v_a_2601_, v___y_2603_);
v_init_2581_ = v___x_2604_;
v_x_2582_ = v_r_2594_;
v___y_2584_ = v_snd_2600_;
goto _start;
}
v___jp_2606_:
{
if (lean_obj_tag(v___y_2607_) == 7)
{
lean_object* v_val_2608_; uint8_t v_isUnsafe_2609_; 
v_val_2608_ = lean_ctor_get(v___y_2607_, 0);
lean_inc_ref(v_val_2608_);
lean_dec_ref_known(v___y_2607_, 1);
v_isUnsafe_2609_ = lean_ctor_get_uint8(v_val_2608_, sizeof(void*)*7 + 1);
if (v_isUnsafe_2609_ == 0)
{
v___y_2603_ = v_val_2608_;
goto v___jp_2602_;
}
else
{
if (v___x_2580_ == 0)
{
uint8_t v_exportUnsafe_2610_; 
v_exportUnsafe_2610_ = lean_ctor_get_uint8(v_snd_2600_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
lean_dec_ref(v_val_2608_);
lean_dec(v_a_2601_);
v___x_2611_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2);
v___x_2612_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v___x_2611_, v___y_2583_, v_snd_2600_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v_fst_2614_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v_fst_2614_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_fst_2614_);
if (lean_obj_tag(v_fst_2614_) == 0)
{
lean_object* v_snd_2615_; lean_object* v_a_2616_; 
lean_dec(v_r_2594_);
v_snd_2615_ = lean_ctor_get(v_a_2613_, 1);
lean_inc(v_snd_2615_);
lean_dec(v_a_2613_);
v_a_2616_ = lean_ctor_get(v_fst_2614_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v_fst_2614_, 1);
v_d_2587_ = v_a_2616_;
v___y_2588_ = v_snd_2615_;
goto v___jp_2586_;
}
else
{
lean_object* v_snd_2617_; lean_object* v_a_2618_; 
v_snd_2617_ = lean_ctor_get(v_a_2613_, 1);
lean_inc(v_snd_2617_);
lean_dec(v_a_2613_);
v_a_2618_ = lean_ctor_get(v_fst_2614_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v_fst_2614_, 1);
v_init_2581_ = v_a_2618_;
v_x_2582_ = v_r_2594_;
v___y_2584_ = v_snd_2617_;
goto _start;
}
}
else
{
lean_dec(v_r_2594_);
return v___x_2612_;
}
}
else
{
v___y_2603_ = v_val_2608_;
goto v___jp_2602_;
}
}
else
{
v___y_2603_ = v_val_2608_;
goto v___jp_2602_;
}
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec_ref(v___y_2607_);
v___x_2620_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4);
v___x_2621_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2620_, v___y_2583_, v_snd_2600_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v_snd_2623_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v_snd_2623_ = lean_ctor_get(v_a_2622_, 1);
lean_inc(v_snd_2623_);
lean_dec(v_a_2622_);
v_init_2581_ = v_a_2601_;
v_x_2582_ = v_r_2594_;
v___y_2584_ = v_snd_2623_;
goto _start;
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_a_2601_);
lean_dec(v_r_2594_);
v_a_2625_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2621_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2621_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
}
else
{
lean_dec(v_r_2594_);
lean_dec(v_k_2592_);
return v___x_2595_;
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_init_2581_);
v___x_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___y_2584_);
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
return v___x_2639_;
}
v___jp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2589_, 0, v_d_2587_);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v___y_2588_);
v___x_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
return v___x_2591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object* v___x_2640_, lean_object* v_init_2641_, lean_object* v_x_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
uint8_t v___x_172041__boxed_2646_; lean_object* v_res_2647_; 
v___x_172041__boxed_2646_ = lean_unbox(v___x_2640_);
v_res_2647_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15(v___x_172041__boxed_2646_, v_init_2641_, v_x_2642_, v___y_2643_, v___y_2644_);
lean_dec_ref(v___y_2643_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object* v_t_2648_, lean_object* v_k_2649_){
_start:
{
if (lean_obj_tag(v_t_2648_) == 0)
{
lean_object* v_k_2650_; lean_object* v_v_2651_; lean_object* v_l_2652_; lean_object* v_r_2653_; uint8_t v___x_2654_; 
v_k_2650_ = lean_ctor_get(v_t_2648_, 1);
v_v_2651_ = lean_ctor_get(v_t_2648_, 2);
v_l_2652_ = lean_ctor_get(v_t_2648_, 3);
v_r_2653_ = lean_ctor_get(v_t_2648_, 4);
v___x_2654_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2649_, v_k_2650_);
switch(v___x_2654_)
{
case 0:
{
v_t_2648_ = v_l_2652_;
goto _start;
}
case 1:
{
lean_object* v___x_2656_; 
lean_inc(v_v_2651_);
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_v_2651_);
return v___x_2656_;
}
default: 
{
v_t_2648_ = v_r_2653_;
goto _start;
}
}
}
else
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_box(0);
return v___x_2658_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object* v_t_2659_, lean_object* v_k_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_2659_, v_k_2660_);
lean_dec(v_k_2660_);
lean_dec(v_t_2659_);
return v_res_2661_;
}
}
static lean_object* _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Array_instInhabited(lean_box(0));
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object* v_msg_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; lean_object* v___f_2668_; lean_object* v___f_2669_; lean_object* v___f_2670_; lean_object* v___f_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___f_2681_; lean_object* v___x_163477__overap_2682_; lean_object* v___x_2683_; 
v___x_2667_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2668_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2668_, 0, v___x_2667_);
v___f_2669_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2669_, 0, v___x_2667_);
v___f_2670_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2670_, 0, v___x_2667_);
v___f_2671_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2671_, 0, v___x_2667_);
v___x_2672_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2672_, 0, lean_box(0));
lean_closure_set(v___x_2672_, 1, lean_box(0));
lean_closure_set(v___x_2672_, 2, v___x_2667_);
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
lean_ctor_set(v___x_2673_, 1, v___f_2668_);
v___x_2674_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2674_, 0, lean_box(0));
lean_closure_set(v___x_2674_, 1, lean_box(0));
lean_closure_set(v___x_2674_, 2, v___x_2667_);
v___x_2675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
lean_ctor_set(v___x_2675_, 2, v___f_2669_);
lean_ctor_set(v___x_2675_, 3, v___f_2670_);
lean_ctor_set(v___x_2675_, 4, v___f_2671_);
v___x_2676_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2676_, 0, lean_box(0));
lean_closure_set(v___x_2676_, 1, lean_box(0));
lean_closure_set(v___x_2676_, 2, v___x_2667_);
v___x_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2675_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
v___x_2680_ = l_instInhabitedOfMonad___redArg(v___x_2677_, v___x_2679_);
v___f_2681_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2681_, 0, v___x_2680_);
v___x_163477__overap_2682_ = lean_panic_fn_borrowed(v___f_2681_, v_msg_2663_);
lean_dec_ref(v___f_2681_);
lean_inc_ref(v___y_2664_);
v___x_2683_ = lean_apply_3(v___x_163477__overap_2682_, v___y_2664_, v___y_2665_, lean_box(0));
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object* v_msg_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v_msg_2684_, v___y_2685_, v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2688_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2690_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2691_ = lean_unsigned_to_nat(10u);
v___x_2692_ = lean_unsigned_to_nat(334u);
v___x_2693_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_2694_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2695_ = l_mkPanicMessageWithDecl(v___x_2694_, v___x_2693_, v___x_2692_, v___x_2691_, v___x_2690_);
return v___x_2695_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2697_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2));
v___x_2698_ = lean_unsigned_to_nat(15u);
v___x_2699_ = lean_unsigned_to_nat(336u);
v___x_2700_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_2701_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2702_ = l_mkPanicMessageWithDecl(v___x_2701_, v___x_2700_, v___x_2699_, v___x_2698_, v___x_2697_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t v___y_2703_, uint8_t v___x_2704_, lean_object* v_as_x27_2705_, lean_object* v_b_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
if (lean_obj_tag(v_as_x27_2705_) == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_b_2706_);
lean_ctor_set(v___x_2710_, 1, v___y_2708_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
else
{
lean_object* v_head_2712_; lean_object* v_tail_2713_; lean_object* v___y_2715_; lean_object* v___y_2719_; uint8_t v___y_2720_; lean_object* v___y_2755_; lean_object* v___x_2771_; 
v_head_2712_ = lean_ctor_get(v_as_x27_2705_, 0);
v_tail_2713_ = lean_ctor_get(v_as_x27_2705_, 1);
lean_inc(v_head_2712_);
lean_inc_ref(v___y_2707_);
v___x_2771_ = l_Lean_Environment_find_x3f(v___y_2707_, v_head_2712_, v___x_2704_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8);
v___x_2773_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2772_);
v___y_2755_ = v___x_2773_;
goto v___jp_2754_;
}
else
{
lean_object* v_val_2774_; 
v_val_2774_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_val_2774_);
lean_dec_ref_known(v___x_2771_, 1);
v___y_2755_ = v_val_2774_;
goto v___jp_2754_;
}
v___jp_2714_:
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_array_push(v_b_2706_, v___y_2715_);
v_as_x27_2705_ = v_tail_2713_;
v_b_2706_ = v___x_2716_;
goto _start;
}
v___jp_2718_:
{
if (v___y_2720_ == 0)
{
uint8_t v_exportUnsafe_2721_; 
v_exportUnsafe_2721_ = lean_ctor_get_uint8(v___y_2708_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_dec_ref(v___y_2719_);
lean_dec_ref(v_b_2706_);
v___x_2722_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1);
v___x_2723_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v___x_2722_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2745_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2745_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2745_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v_fst_2728_; 
v_fst_2728_ = lean_ctor_get(v_a_2724_, 0);
lean_inc(v_fst_2728_);
if (lean_obj_tag(v_fst_2728_) == 0)
{
lean_object* v_snd_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2740_; 
v_snd_2729_ = lean_ctor_get(v_a_2724_, 1);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_a_2724_);
if (v_isSharedCheck_2740_ == 0)
{
lean_object* v_unused_2741_; 
v_unused_2741_ = lean_ctor_get(v_a_2724_, 0);
lean_dec(v_unused_2741_);
v___x_2731_ = v_a_2724_;
v_isShared_2732_ = v_isSharedCheck_2740_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_snd_2729_);
lean_dec(v_a_2724_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2740_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v_a_2733_; lean_object* v___x_2735_; 
v_a_2733_ = lean_ctor_get(v_fst_2728_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v_fst_2728_, 1);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v_a_2733_);
v___x_2735_ = v___x_2731_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_snd_2729_);
v___x_2735_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2737_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v___x_2735_);
v___x_2737_ = v___x_2726_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
else
{
lean_object* v_snd_2742_; lean_object* v_a_2743_; 
lean_del_object(v___x_2726_);
v_snd_2742_ = lean_ctor_get(v_a_2724_, 1);
lean_inc(v_snd_2742_);
lean_dec(v_a_2724_);
v_a_2743_ = lean_ctor_get(v_fst_2728_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v_fst_2728_, 1);
v_as_x27_2705_ = v_tail_2713_;
v_b_2706_ = v_a_2743_;
v___y_2708_ = v_snd_2742_;
goto _start;
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
v_a_2746_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2723_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2723_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
else
{
v___y_2715_ = v___y_2719_;
goto v___jp_2714_;
}
}
else
{
v___y_2715_ = v___y_2719_;
goto v___jp_2714_;
}
}
v___jp_2754_:
{
if (lean_obj_tag(v___y_2755_) == 6)
{
lean_object* v_val_2756_; uint8_t v_isUnsafe_2757_; 
v_val_2756_ = lean_ctor_get(v___y_2755_, 0);
lean_inc_ref(v_val_2756_);
lean_dec_ref_known(v___y_2755_, 1);
v_isUnsafe_2757_ = lean_ctor_get_uint8(v_val_2756_, sizeof(void*)*5);
if (v_isUnsafe_2757_ == 0)
{
v___y_2719_ = v_val_2756_;
v___y_2720_ = v___y_2703_;
goto v___jp_2718_;
}
else
{
v___y_2719_ = v_val_2756_;
v___y_2720_ = v___x_2704_;
goto v___jp_2718_;
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_dec_ref(v___y_2755_);
v___x_2758_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3);
v___x_2759_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2758_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v_snd_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
v_snd_2761_ = lean_ctor_get(v_a_2760_, 1);
lean_inc(v_snd_2761_);
lean_dec(v_a_2760_);
v_as_x27_2705_ = v_tail_2713_;
v___y_2708_ = v_snd_2761_;
goto _start;
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v_b_2706_);
v_a_2763_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2759_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2759_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object* v___y_2775_, lean_object* v___x_2776_, lean_object* v_as_x27_2777_, lean_object* v_b_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
uint8_t v___y_172292__boxed_2782_; uint8_t v___x_172293__boxed_2783_; lean_object* v_res_2784_; 
v___y_172292__boxed_2782_ = lean_unbox(v___y_2775_);
v___x_172293__boxed_2783_ = lean_unbox(v___x_2776_);
v_res_2784_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_172292__boxed_2782_, v___x_172293__boxed_2783_, v_as_x27_2777_, v_b_2778_, v___y_2779_, v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v_as_x27_2777_);
return v_res_2784_;
}
}
static lean_object* _init_l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0(void){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Array_instInhabited(lean_box(0));
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object* v_msg_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; lean_object* v___f_2791_; lean_object* v___f_2792_; lean_object* v___f_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___f_2807_; lean_object* v___x_164159__overap_2808_; lean_object* v___x_2809_; 
v___x_2790_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2791_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2791_, 0, v___x_2790_);
v___f_2792_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2792_, 0, v___x_2790_);
v___f_2793_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2793_, 0, v___x_2790_);
v___f_2794_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2794_, 0, v___x_2790_);
v___x_2795_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2795_, 0, lean_box(0));
lean_closure_set(v___x_2795_, 1, lean_box(0));
lean_closure_set(v___x_2795_, 2, v___x_2790_);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___f_2791_);
v___x_2797_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2797_, 0, lean_box(0));
lean_closure_set(v___x_2797_, 1, lean_box(0));
lean_closure_set(v___x_2797_, 2, v___x_2790_);
v___x_2798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
lean_ctor_set(v___x_2798_, 2, v___f_2792_);
lean_ctor_set(v___x_2798_, 3, v___f_2793_);
lean_ctor_set(v___x_2798_, 4, v___f_2794_);
v___x_2799_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2799_, 0, lean_box(0));
lean_closure_set(v___x_2799_, 1, lean_box(0));
lean_closure_set(v___x_2799_, 2, v___x_2790_);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0);
v___x_2802_ = lean_box(1);
v___x_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2801_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
v___x_2806_ = l_instInhabitedOfMonad___redArg(v___x_2800_, v___x_2805_);
v___f_2807_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2807_, 0, v___x_2806_);
v___x_164159__overap_2808_ = lean_panic_fn_borrowed(v___f_2807_, v_msg_2786_);
lean_dec_ref(v___f_2807_);
lean_inc_ref(v___y_2787_);
v___x_2809_ = lean_apply_3(v___x_164159__overap_2808_, v___y_2787_, v___y_2788_, lean_box(0));
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object* v_msg_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v_msg_2810_, v___y_2811_, v___y_2812_);
lean_dec_ref(v___y_2811_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25(size_t v_sz_2815_, size_t v_i_2816_, lean_object* v_bs_2817_){
_start:
{
uint8_t v___x_2818_; 
v___x_2818_ = lean_usize_dec_lt(v_i_2816_, v_sz_2815_);
if (v___x_2818_ == 0)
{
return v_bs_2817_;
}
else
{
lean_object* v_v_2819_; lean_object* v___x_2820_; lean_object* v_bs_x27_2821_; size_t v___x_2822_; size_t v___x_2823_; lean_object* v___x_2824_; 
v_v_2819_ = lean_array_uget(v_bs_2817_, v_i_2816_);
v___x_2820_ = lean_unsigned_to_nat(0u);
v_bs_x27_2821_ = lean_array_uset(v_bs_2817_, v_i_2816_, v___x_2820_);
v___x_2822_ = ((size_t)1ULL);
v___x_2823_ = lean_usize_add(v_i_2816_, v___x_2822_);
v___x_2824_ = lean_array_uset(v_bs_x27_2821_, v_i_2816_, v_v_2819_);
v_i_2816_ = v___x_2823_;
v_bs_2817_ = v___x_2824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25___boxed(lean_object* v_sz_2826_, lean_object* v_i_2827_, lean_object* v_bs_2828_){
_start:
{
size_t v_sz_boxed_2829_; size_t v_i_boxed_2830_; lean_object* v_res_2831_; 
v_sz_boxed_2829_ = lean_unbox_usize(v_sz_2826_);
lean_dec(v_sz_2826_);
v_i_boxed_2830_ = lean_unbox_usize(v_i_2827_);
lean_dec(v_i_2827_);
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25(v_sz_boxed_2829_, v_i_boxed_2830_, v_bs_2828_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(lean_object* v_a_2832_){
_start:
{
size_t v_sz_2833_; size_t v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v_sz_2833_ = lean_array_size(v_a_2832_);
v___x_2834_ = ((size_t)0ULL);
v___x_2835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25(v_sz_2833_, v___x_2834_, v_a_2832_);
v___x_2836_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object* v_a_2837_){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = lean_array_mk(v_a_2837_);
v___x_2839_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(v___x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16(lean_object* v_as_2840_, size_t v_sz_2841_, size_t v_i_2842_, lean_object* v_b_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_usize_dec_lt(v_i_2842_, v_sz_2841_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2848_, 0, v_b_2843_);
lean_ctor_set(v___x_2848_, 1, v___y_2845_);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
else
{
lean_object* v_visitedNames_2850_; lean_object* v_visitedLevels_2851_; lean_object* v_visitedExprs_2852_; lean_object* v_visitedConstants_2853_; lean_object* v_noMDataExprs_2854_; uint8_t v_exportMData_2855_; uint8_t v_exportUnsafe_2856_; uint8_t v_ignoreMissing_2857_; lean_object* v_recursorMap_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2877_; 
v_visitedNames_2850_ = lean_ctor_get(v___y_2845_, 0);
v_visitedLevels_2851_ = lean_ctor_get(v___y_2845_, 1);
v_visitedExprs_2852_ = lean_ctor_get(v___y_2845_, 2);
v_visitedConstants_2853_ = lean_ctor_get(v___y_2845_, 3);
v_noMDataExprs_2854_ = lean_ctor_get(v___y_2845_, 4);
v_exportMData_2855_ = lean_ctor_get_uint8(v___y_2845_, sizeof(void*)*6);
v_exportUnsafe_2856_ = lean_ctor_get_uint8(v___y_2845_, sizeof(void*)*6 + 1);
v_ignoreMissing_2857_ = lean_ctor_get_uint8(v___y_2845_, sizeof(void*)*6 + 2);
v_recursorMap_2858_ = lean_ctor_get(v___y_2845_, 5);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___y_2845_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2860_ = v___y_2845_;
v_isShared_2861_ = v_isSharedCheck_2877_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_recursorMap_2858_);
lean_inc(v_noMDataExprs_2854_);
lean_inc(v_visitedConstants_2853_);
lean_inc(v_visitedExprs_2852_);
lean_inc(v_visitedLevels_2851_);
lean_inc(v_visitedNames_2850_);
lean_dec(v___y_2845_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2877_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v_a_2862_; lean_object* v_toConstantVal_2863_; lean_object* v_name_2864_; lean_object* v_type_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v_a_2862_ = lean_array_uget_borrowed(v_as_2840_, v_i_2842_);
v_toConstantVal_2863_ = lean_ctor_get(v_a_2862_, 0);
v_name_2864_ = lean_ctor_get(v_toConstantVal_2863_, 0);
v_type_2865_ = lean_ctor_get(v_toConstantVal_2863_, 2);
lean_inc(v_name_2864_);
v___x_2866_ = l_Lean_NameHashSet_insert(v_visitedConstants_2853_, v_name_2864_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 3, v___x_2866_);
v___x_2868_ = v___x_2860_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_visitedNames_2850_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_visitedLevels_2851_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_visitedExprs_2852_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v_noMDataExprs_2854_);
lean_ctor_set(v_reuseFailAlloc_2876_, 5, v_recursorMap_2858_);
lean_ctor_set_uint8(v_reuseFailAlloc_2876_, sizeof(void*)*6, v_exportMData_2855_);
lean_ctor_set_uint8(v_reuseFailAlloc_2876_, sizeof(void*)*6 + 1, v_exportUnsafe_2856_);
lean_ctor_set_uint8(v_reuseFailAlloc_2876_, sizeof(void*)*6 + 2, v_ignoreMissing_2857_);
v___x_2868_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; 
lean_inc_ref(v_type_2865_);
v___x_2869_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_2865_, v___y_2844_, v___x_2868_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v_snd_2871_; lean_object* v___x_2872_; size_t v___x_2873_; size_t v___x_2874_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v_snd_2871_ = lean_ctor_get(v_a_2870_, 1);
lean_inc(v_snd_2871_);
lean_dec(v_a_2870_);
v___x_2872_ = lean_box(0);
v___x_2873_ = ((size_t)1ULL);
v___x_2874_ = lean_usize_add(v_i_2842_, v___x_2873_);
v_i_2842_ = v___x_2874_;
v_b_2843_ = v___x_2872_;
v___y_2845_ = v_snd_2871_;
goto _start;
}
else
{
return v___x_2869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object* v_as_x27_2878_, lean_object* v_b_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
if (lean_obj_tag(v_as_x27_2878_) == 0)
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_b_2879_);
lean_ctor_set(v___x_2883_, 1, v___y_2881_);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
else
{
lean_object* v_head_2885_; lean_object* v_tail_2886_; lean_object* v_rhs_2887_; lean_object* v___x_2888_; 
v_head_2885_ = lean_ctor_get(v_as_x27_2878_, 0);
v_tail_2886_ = lean_ctor_get(v_as_x27_2878_, 1);
v_rhs_2887_ = lean_ctor_get(v_head_2885_, 2);
lean_inc_ref(v_rhs_2887_);
v___x_2888_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_rhs_2887_, v___y_2880_, v___y_2881_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v_snd_2890_; lean_object* v___x_2891_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2888_, 1);
v_snd_2890_ = lean_ctor_get(v_a_2889_, 1);
lean_inc(v_snd_2890_);
lean_dec(v_a_2889_);
v___x_2891_ = lean_box(0);
v_as_x27_2878_ = v_tail_2886_;
v_b_2879_ = v___x_2891_;
v___y_2881_ = v_snd_2890_;
goto _start;
}
else
{
return v___x_2888_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17(lean_object* v_as_2893_, size_t v_sz_2894_, size_t v_i_2895_, lean_object* v_b_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
uint8_t v___x_2900_; 
v___x_2900_ = lean_usize_dec_lt(v_i_2895_, v_sz_2894_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2901_, 0, v_b_2896_);
lean_ctor_set(v___x_2901_, 1, v___y_2898_);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
else
{
lean_object* v_a_2903_; lean_object* v_rules_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_a_2903_ = lean_array_uget_borrowed(v_as_2893_, v_i_2895_);
v_rules_2904_ = lean_ctor_get(v_a_2903_, 6);
v___x_2905_ = lean_box(0);
v___x_2906_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_rules_2904_, v___x_2905_, v___y_2897_, v___y_2898_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v_snd_2908_; size_t v___x_2909_; size_t v___x_2910_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref_known(v___x_2906_, 1);
v_snd_2908_ = lean_ctor_get(v_a_2907_, 1);
lean_inc(v_snd_2908_);
lean_dec(v_a_2907_);
v___x_2909_ = ((size_t)1ULL);
v___x_2910_ = lean_usize_add(v_i_2895_, v___x_2909_);
v_i_2895_ = v___x_2910_;
v_b_2896_ = v___x_2905_;
v___y_2898_ = v_snd_2908_;
goto _start;
}
else
{
return v___x_2906_;
}
}
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__0(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_unsigned_to_nat(16u);
v___x_2914_ = lean_mk_array(v___x_2913_, v___x_2912_);
return v___x_2914_;
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__1(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__0, &l_LeanExport_dumpExpr___closed__0_once, _init_l_LeanExport_dumpExpr___closed__0);
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
lean_ctor_set(v___x_2917_, 1, v___x_2915_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v_visitedConstants_2944_; lean_object* v_nat_2945_; uint8_t v___x_2946_; 
v_visitedConstants_2944_ = lean_ctor_get(v_a_2938_, 3);
v_nat_2945_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1));
v___x_2946_ = l_Lean_NameHashSet_contains(v_visitedConstants_2944_, v_nat_2945_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; 
lean_inc_ref(v_a_2937_);
v___x_2947_ = l_Lean_Environment_find_x3f(v_a_2937_, v_nat_2945_, v___x_2946_);
if (lean_obj_tag(v___x_2947_) == 0)
{
goto v___jp_2940_;
}
else
{
lean_object* v___x_2948_; 
lean_dec_ref_known(v___x_2947_, 1);
v___x_2948_ = l_LeanExport_dumpConstant(v_nat_2945_, v_a_2937_, v_a_2938_);
return v___x_2948_;
}
}
else
{
goto v___jp_2940_;
}
v___jp_2940_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v_a_2938_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
return v___x_2943_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___y_2964_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v_visitedConstants_2971_; lean_object* v_visitedConstants_2976_; lean_object* v_charOfNat_2977_; uint8_t v___x_2978_; 
v_visitedConstants_2976_ = lean_ctor_get(v_a_2961_, 3);
v_charOfNat_2977_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5));
v___x_2978_ = l_Lean_NameHashSet_contains(v_visitedConstants_2976_, v_charOfNat_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
lean_inc_ref(v_a_2960_);
v___x_2979_ = l_Lean_Environment_find_x3f(v_a_2960_, v_charOfNat_2977_, v___x_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_inc_ref(v_visitedConstants_2976_);
v___y_2969_ = v_a_2960_;
v___y_2970_ = v_a_2961_;
v_visitedConstants_2971_ = v_visitedConstants_2976_;
goto v___jp_2968_;
}
else
{
lean_object* v___x_2980_; 
lean_dec_ref_known(v___x_2979_, 1);
v___x_2980_ = l_LeanExport_dumpConstant(v_charOfNat_2977_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v_snd_2982_; lean_object* v_visitedConstants_2983_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v_snd_2982_ = lean_ctor_get(v_a_2981_, 1);
lean_inc(v_snd_2982_);
lean_dec(v_a_2981_);
v_visitedConstants_2983_ = lean_ctor_get(v_snd_2982_, 3);
lean_inc_ref(v_visitedConstants_2983_);
v___y_2969_ = v_a_2960_;
v___y_2970_ = v_snd_2982_;
v_visitedConstants_2971_ = v_visitedConstants_2983_;
goto v___jp_2968_;
}
else
{
return v___x_2980_;
}
}
}
else
{
lean_inc_ref(v_visitedConstants_2976_);
v___y_2969_ = v_a_2960_;
v___y_2970_ = v_a_2961_;
v_visitedConstants_2971_ = v_visitedConstants_2976_;
goto v___jp_2968_;
}
v___jp_2963_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = lean_box(0);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v___y_2964_);
v___x_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
return v___x_2967_;
}
v___jp_2968_:
{
lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2));
v___x_2973_ = l_Lean_NameHashSet_contains(v_visitedConstants_2971_, v___x_2972_);
lean_dec_ref(v_visitedConstants_2971_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_inc_ref(v___y_2969_);
v___x_2974_ = l_Lean_Environment_find_x3f(v___y_2969_, v___x_2972_, v___x_2973_);
if (lean_obj_tag(v___x_2974_) == 0)
{
v___y_2964_ = v___y_2970_;
goto v___jp_2963_;
}
else
{
lean_object* v___x_2975_; 
lean_dec_ref_known(v___x_2974_, 1);
v___x_2975_ = l_LeanExport_dumpConstant(v___x_2972_, v___y_2969_, v___y_2970_);
return v___x_2975_;
}
}
else
{
v___y_2964_ = v___y_2970_;
goto v___jp_2963_;
}
}
}
}
static lean_object* _init_l_LeanExport_dumpExprAux___closed__26(void){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2994_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__25));
v___x_2995_ = lean_unsigned_to_nat(29u);
v___x_2996_ = lean_unsigned_to_nat(177u);
v___x_2997_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__24));
v___x_2998_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2999_ = l_mkPanicMessageWithDecl(v___x_2998_, v___x_2997_, v___x_2996_, v___x_2995_, v___x_2994_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux(lean_object* v_e_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v_visitedNames_3004_; lean_object* v_visitedLevels_3005_; lean_object* v_visitedExprs_3006_; lean_object* v_visitedConstants_3007_; lean_object* v_noMDataExprs_3008_; uint8_t v_exportMData_3009_; uint8_t v_exportUnsafe_3010_; uint8_t v_ignoreMissing_3011_; lean_object* v_recursorMap_3012_; lean_object* v___x_3013_; 
v_visitedNames_3004_ = lean_ctor_get(v_a_3002_, 0);
v_visitedLevels_3005_ = lean_ctor_get(v_a_3002_, 1);
v_visitedExprs_3006_ = lean_ctor_get(v_a_3002_, 2);
v_visitedConstants_3007_ = lean_ctor_get(v_a_3002_, 3);
v_noMDataExprs_3008_ = lean_ctor_get(v_a_3002_, 4);
v_exportMData_3009_ = lean_ctor_get_uint8(v_a_3002_, sizeof(void*)*6);
v_exportUnsafe_3010_ = lean_ctor_get_uint8(v_a_3002_, sizeof(void*)*6 + 1);
v_ignoreMissing_3011_ = lean_ctor_get_uint8(v_a_3002_, sizeof(void*)*6 + 2);
v_recursorMap_3012_ = lean_ctor_get(v_a_3002_, 5);
v___x_3013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_visitedExprs_3006_, v_e_3000_);
if (lean_obj_tag(v___x_3013_) == 1)
{
lean_object* v_val_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v_e_3000_);
v_val_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3022_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_val_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3022_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v_val_3014_);
lean_ctor_set(v___x_3018_, 1, v_a_3002_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set_tag(v___x_3016_, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3018_);
v___x_3020_ = v___x_3016_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v___x_3023_; lean_object* v_fst_3025_; lean_object* v_visitedNames_3026_; lean_object* v_visitedLevels_3027_; lean_object* v_visitedExprs_3028_; lean_object* v_visitedConstants_3029_; lean_object* v_noMDataExprs_3030_; uint8_t v_exportMData_3031_; uint8_t v_exportUnsafe_3032_; uint8_t v_ignoreMissing_3033_; lean_object* v_recursorMap_3034_; lean_object* v_fst_3061_; lean_object* v_snd_3062_; 
lean_dec(v___x_3013_);
v___x_3023_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__0));
switch(lean_obj_tag(v_e_3000_))
{
case 0:
{
lean_object* v_deBruijnIndex_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_inc(v_recursorMap_3012_);
lean_inc_ref(v_noMDataExprs_3008_);
lean_inc_ref(v_visitedConstants_3007_);
lean_inc_ref(v_visitedExprs_3006_);
lean_inc_ref(v_visitedLevels_3005_);
lean_inc_ref(v_visitedNames_3004_);
lean_dec_ref(v_a_3002_);
v_deBruijnIndex_3072_ = lean_ctor_get(v_e_3000_, 0);
v___x_3073_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__1));
lean_inc(v_deBruijnIndex_3072_);
v___x_3074_ = l_Lean_JsonNumber_fromNat(v_deBruijnIndex_3072_);
v___x_3075_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3073_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = l_Lean_Json_mkObj(v___x_3078_);
lean_dec_ref_known(v___x_3078_, 2);
v_fst_3025_ = v___x_3079_;
v_visitedNames_3026_ = v_visitedNames_3004_;
v_visitedLevels_3027_ = v_visitedLevels_3005_;
v_visitedExprs_3028_ = v_visitedExprs_3006_;
v_visitedConstants_3029_ = v_visitedConstants_3007_;
v_noMDataExprs_3030_ = v_noMDataExprs_3008_;
v_exportMData_3031_ = v_exportMData_3009_;
v_exportUnsafe_3032_ = v_exportUnsafe_3010_;
v_ignoreMissing_3033_ = v_ignoreMissing_3011_;
v_recursorMap_3034_ = v_recursorMap_3012_;
goto v___jp_3024_;
}
case 3:
{
lean_object* v_u_3080_; lean_object* v___x_3081_; 
v_u_3080_ = lean_ctor_get(v_e_3000_, 0);
lean_inc(v_u_3080_);
v___x_3081_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_u_3080_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3103_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3103_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3103_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v_fst_3086_; lean_object* v_snd_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3102_; 
v_fst_3086_ = lean_ctor_get(v_a_3082_, 0);
v_snd_3087_ = lean_ctor_get(v_a_3082_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_a_3082_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3089_ = v_a_3082_;
v_isShared_3090_ = v_isSharedCheck_3102_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_snd_3087_);
lean_inc(v_fst_3086_);
lean_dec(v_a_3082_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3102_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3094_; 
v___x_3091_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__2));
v___x_3092_ = l_Lean_JsonNumber_fromNat(v_fst_3086_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set_tag(v___x_3084_, 2);
lean_ctor_set(v___x_3084_, 0, v___x_3092_);
v___x_3094_ = v___x_3084_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3096_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 1, v___x_3094_);
lean_ctor_set(v___x_3089_, 0, v___x_3091_);
v___x_3096_ = v___x_3089_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = lean_box(0);
v___x_3098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_Json_mkObj(v___x_3098_);
lean_dec_ref_known(v___x_3098_, 2);
v_fst_3061_ = v___x_3099_;
v_snd_3062_ = v_snd_3087_;
goto v___jp_3060_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3000_, 1);
return v___x_3081_;
}
}
case 4:
{
lean_object* v_declName_3104_; lean_object* v_us_3105_; lean_object* v___x_3106_; 
v_declName_3104_ = lean_ctor_get(v_e_3000_, 0);
v_us_3105_ = lean_ctor_get(v_e_3000_, 1);
lean_inc(v_declName_3104_);
v___x_3106_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3104_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3154_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3154_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3154_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v_fst_3111_; lean_object* v_snd_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3153_; 
v_fst_3111_ = lean_ctor_get(v_a_3107_, 0);
v_snd_3112_ = lean_ctor_get(v_a_3107_, 1);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_a_3107_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3114_ = v_a_3107_;
v_isShared_3115_ = v_isSharedCheck_3153_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_snd_3112_);
lean_inc(v_fst_3111_);
lean_dec(v_a_3107_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3153_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_box(0);
lean_inc(v_us_3105_);
v___x_3117_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_us_3105_, v___x_3116_, v_a_3001_, v_snd_3112_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v_fst_3119_; lean_object* v_snd_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3144_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v_fst_3119_ = lean_ctor_get(v_a_3118_, 0);
v_snd_3120_ = lean_ctor_get(v_a_3118_, 1);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_a_3118_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3122_ = v_a_3118_;
v_isShared_3123_ = v_isSharedCheck_3144_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_snd_3120_);
lean_inc(v_fst_3119_);
lean_dec(v_a_3118_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3144_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3124_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__3));
v___x_3125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3126_ = l_Lean_JsonNumber_fromNat(v_fst_3111_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set_tag(v___x_3109_, 2);
lean_ctor_set(v___x_3109_, 0, v___x_3126_);
v___x_3128_ = v___x_3109_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3130_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 1, v___x_3128_);
lean_ctor_set(v___x_3122_, 0, v___x_3125_);
v___x_3130_ = v___x_3122_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3131_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__4));
v___x_3132_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_3119_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 1, v___x_3132_);
lean_ctor_set(v___x_3114_, 0, v___x_3131_);
v___x_3134_ = v___x_3114_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
lean_ctor_set(v___x_3135_, 1, v___x_3116_);
v___x_3136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3130_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_Json_mkObj(v___x_3136_);
lean_dec_ref_known(v___x_3136_, 2);
v___x_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3124_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
lean_ctor_set(v___x_3139_, 1, v___x_3116_);
v___x_3140_ = l_Lean_Json_mkObj(v___x_3139_);
lean_dec_ref_known(v___x_3139_, 2);
v_fst_3061_ = v___x_3140_;
v_snd_3062_ = v_snd_3120_;
goto v___jp_3060_;
}
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_del_object(v___x_3114_);
lean_dec(v_fst_3111_);
lean_del_object(v___x_3109_);
lean_dec_ref_known(v_e_3000_, 2);
v_a_3145_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3117_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3117_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3000_, 2);
return v___x_3106_;
}
}
case 5:
{
lean_object* v_fn_3155_; lean_object* v_arg_3156_; lean_object* v___x_3157_; 
v_fn_3155_ = lean_ctor_get(v_e_3000_, 0);
v_arg_3156_ = lean_ctor_get(v_e_3000_, 1);
lean_inc_ref(v_fn_3155_);
v___x_3157_ = l_LeanExport_dumpExprAux(v_fn_3155_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3204_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3204_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3204_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_fst_3162_; lean_object* v_snd_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3203_; 
v_fst_3162_ = lean_ctor_get(v_a_3158_, 0);
v_snd_3163_ = lean_ctor_get(v_a_3158_, 1);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_a_3158_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3165_ = v_a_3158_;
v_isShared_3166_ = v_isSharedCheck_3203_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_snd_3163_);
lean_inc(v_fst_3162_);
lean_dec(v_a_3158_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3203_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; 
lean_inc_ref(v_arg_3156_);
v___x_3167_ = l_LeanExport_dumpExprAux(v_arg_3156_, v_a_3001_, v_snd_3163_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3202_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3202_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3202_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_fst_3172_; lean_object* v_snd_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3201_; 
v_fst_3172_ = lean_ctor_get(v_a_3168_, 0);
v_snd_3173_ = lean_ctor_get(v_a_3168_, 1);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_a_3168_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3175_ = v_a_3168_;
v_isShared_3176_ = v_isSharedCheck_3201_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_snd_3173_);
lean_inc(v_fst_3172_);
lean_dec(v_a_3168_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3201_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3177_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__5));
v___x_3178_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__6));
v___x_3179_ = l_Lean_JsonNumber_fromNat(v_fst_3162_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set_tag(v___x_3170_, 2);
lean_ctor_set(v___x_3170_, 0, v___x_3179_);
v___x_3181_ = v___x_3170_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3183_; 
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 1, v___x_3181_);
lean_ctor_set(v___x_3175_, 0, v___x_3178_);
v___x_3183_ = v___x_3175_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3184_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__7));
v___x_3185_ = l_Lean_JsonNumber_fromNat(v_fst_3172_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set_tag(v___x_3160_, 2);
lean_ctor_set(v___x_3160_, 0, v___x_3185_);
v___x_3187_ = v___x_3160_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3189_; 
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 1, v___x_3187_);
lean_ctor_set(v___x_3165_, 0, v___x_3184_);
v___x_3189_ = v___x_3165_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3190_ = lean_box(0);
v___x_3191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3189_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3183_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = l_Lean_Json_mkObj(v___x_3192_);
lean_dec_ref_known(v___x_3192_, 2);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3177_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
lean_ctor_set(v___x_3195_, 1, v___x_3190_);
v___x_3196_ = l_Lean_Json_mkObj(v___x_3195_);
lean_dec_ref_known(v___x_3195_, 2);
v_fst_3061_ = v___x_3196_;
v_snd_3062_ = v_snd_3173_;
goto v___jp_3060_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3165_);
lean_dec(v_fst_3162_);
lean_del_object(v___x_3160_);
lean_dec_ref_known(v_e_3000_, 2);
return v___x_3167_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3000_, 2);
return v___x_3157_;
}
}
case 6:
{
lean_object* v_binderName_3205_; lean_object* v_binderType_3206_; lean_object* v_body_3207_; uint8_t v_binderInfo_3208_; lean_object* v___x_3209_; 
v_binderName_3205_ = lean_ctor_get(v_e_3000_, 0);
v_binderType_3206_ = lean_ctor_get(v_e_3000_, 1);
v_body_3207_ = lean_ctor_get(v_e_3000_, 2);
v_binderInfo_3208_ = lean_ctor_get_uint8(v_e_3000_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3205_);
v___x_3209_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3205_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3281_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3212_ = v___x_3209_;
v_isShared_3213_ = v_isSharedCheck_3281_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3281_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v_fst_3214_; lean_object* v_snd_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3280_; 
v_fst_3214_ = lean_ctor_get(v_a_3210_, 0);
v_snd_3215_ = lean_ctor_get(v_a_3210_, 1);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_a_3210_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3217_ = v_a_3210_;
v_isShared_3218_ = v_isSharedCheck_3280_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_snd_3215_);
lean_inc(v_fst_3214_);
lean_dec(v_a_3210_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3280_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; 
lean_inc_ref(v_binderType_3206_);
v___x_3219_ = l_LeanExport_dumpExprAux(v_binderType_3206_, v_a_3001_, v_snd_3215_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3279_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3279_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3279_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v_fst_3224_; lean_object* v_snd_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3278_; 
v_fst_3224_ = lean_ctor_get(v_a_3220_, 0);
v_snd_3225_ = lean_ctor_get(v_a_3220_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_a_3220_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3227_ = v_a_3220_;
v_isShared_3228_ = v_isSharedCheck_3278_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_snd_3225_);
lean_inc(v_fst_3224_);
lean_dec(v_a_3220_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3278_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; 
lean_inc_ref(v_body_3207_);
v___x_3229_ = l_LeanExport_dumpExprAux(v_body_3207_, v_a_3001_, v_snd_3225_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3277_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3277_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3277_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v_fst_3234_; lean_object* v_snd_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3276_; 
v_fst_3234_ = lean_ctor_get(v_a_3230_, 0);
v_snd_3235_ = lean_ctor_get(v_a_3230_, 1);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_a_3230_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3237_ = v_a_3230_;
v_isShared_3238_ = v_isSharedCheck_3276_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_snd_3235_);
lean_inc(v_fst_3234_);
lean_dec(v_a_3230_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3276_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
v___x_3239_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__8));
v___x_3240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3241_ = l_Lean_JsonNumber_fromNat(v_fst_3214_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set_tag(v___x_3232_, 2);
lean_ctor_set(v___x_3232_, 0, v___x_3241_);
v___x_3243_ = v___x_3232_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3241_);
v___x_3243_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3245_; 
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 1, v___x_3243_);
lean_ctor_set(v___x_3237_, 0, v___x_3240_);
v___x_3245_ = v___x_3237_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3246_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3247_ = l_Lean_JsonNumber_fromNat(v_fst_3224_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set_tag(v___x_3222_, 2);
lean_ctor_set(v___x_3222_, 0, v___x_3247_);
v___x_3249_ = v___x_3222_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3251_; 
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 1, v___x_3249_);
lean_ctor_set(v___x_3227_, 0, v___x_3246_);
v___x_3251_ = v___x_3227_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3252_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3253_ = l_Lean_JsonNumber_fromNat(v_fst_3234_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set_tag(v___x_3212_, 2);
lean_ctor_set(v___x_3212_, 0, v___x_3253_);
v___x_3255_ = v___x_3212_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3257_; 
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 1, v___x_3255_);
lean_ctor_set(v___x_3217_, 0, v___x_3252_);
v___x_3257_ = v___x_3217_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3252_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3258_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3259_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3208_);
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3260_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3257_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3251_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3245_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = l_Lean_Json_mkObj(v___x_3265_);
lean_dec_ref_known(v___x_3265_, 2);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3239_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
lean_ctor_set(v___x_3268_, 1, v___x_3261_);
v___x_3269_ = l_Lean_Json_mkObj(v___x_3268_);
lean_dec_ref_known(v___x_3268_, 2);
v_fst_3061_ = v___x_3269_;
v_snd_3062_ = v_snd_3235_;
goto v___jp_3060_;
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
lean_del_object(v___x_3227_);
lean_dec(v_fst_3224_);
lean_del_object(v___x_3222_);
lean_del_object(v___x_3217_);
lean_dec(v_fst_3214_);
lean_del_object(v___x_3212_);
lean_dec_ref_known(v_e_3000_, 3);
return v___x_3229_;
}
}
}
}
else
{
lean_del_object(v___x_3217_);
lean_dec(v_fst_3214_);
lean_del_object(v___x_3212_);
lean_dec_ref_known(v_e_3000_, 3);
return v___x_3219_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3000_, 3);
return v___x_3209_;
}
}
case 7:
{
lean_object* v_binderName_3282_; lean_object* v_binderType_3283_; lean_object* v_body_3284_; uint8_t v_binderInfo_3285_; lean_object* v___x_3286_; 
v_binderName_3282_ = lean_ctor_get(v_e_3000_, 0);
v_binderType_3283_ = lean_ctor_get(v_e_3000_, 1);
v_body_3284_ = lean_ctor_get(v_e_3000_, 2);
v_binderInfo_3285_ = lean_ctor_get_uint8(v_e_3000_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3282_);
v___x_3286_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3282_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3358_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3358_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3358_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v_fst_3291_; lean_object* v_snd_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3357_; 
v_fst_3291_ = lean_ctor_get(v_a_3287_, 0);
v_snd_3292_ = lean_ctor_get(v_a_3287_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_a_3287_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3294_ = v_a_3287_;
v_isShared_3295_ = v_isSharedCheck_3357_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_snd_3292_);
lean_inc(v_fst_3291_);
lean_dec(v_a_3287_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3357_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; 
lean_inc_ref(v_binderType_3283_);
v___x_3296_ = l_LeanExport_dumpExprAux(v_binderType_3283_, v_a_3001_, v_snd_3292_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3356_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3356_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3356_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v_fst_3301_; lean_object* v_snd_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3355_; 
v_fst_3301_ = lean_ctor_get(v_a_3297_, 0);
v_snd_3302_ = lean_ctor_get(v_a_3297_, 1);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_a_3297_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3304_ = v_a_3297_;
v_isShared_3305_ = v_isSharedCheck_3355_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_snd_3302_);
lean_inc(v_fst_3301_);
lean_dec(v_a_3297_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3355_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; 
lean_inc_ref(v_body_3284_);
v___x_3306_ = l_LeanExport_dumpExprAux(v_body_3284_, v_a_3001_, v_snd_3302_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3354_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3354_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3354_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v_fst_3311_; lean_object* v_snd_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3353_; 
v_fst_3311_ = lean_ctor_get(v_a_3307_, 0);
v_snd_3312_ = lean_ctor_get(v_a_3307_, 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_a_3307_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3314_ = v_a_3307_;
v_isShared_3315_ = v_isSharedCheck_3353_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_snd_3312_);
lean_inc(v_fst_3311_);
lean_dec(v_a_3307_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3353_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3316_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__11));
v___x_3317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3318_ = l_Lean_JsonNumber_fromNat(v_fst_3291_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set_tag(v___x_3309_, 2);
lean_ctor_set(v___x_3309_, 0, v___x_3318_);
v___x_3320_ = v___x_3309_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
lean_object* v___x_3322_; 
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 1, v___x_3320_);
lean_ctor_set(v___x_3314_, 0, v___x_3317_);
v___x_3322_ = v___x_3314_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3326_; 
v___x_3323_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3324_ = l_Lean_JsonNumber_fromNat(v_fst_3301_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set_tag(v___x_3299_, 2);
lean_ctor_set(v___x_3299_, 0, v___x_3324_);
v___x_3326_ = v___x_3299_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3328_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 1, v___x_3326_);
lean_ctor_set(v___x_3304_, 0, v___x_3323_);
v___x_3328_ = v___x_3304_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3323_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3332_; 
v___x_3329_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3330_ = l_Lean_JsonNumber_fromNat(v_fst_3311_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set_tag(v___x_3289_, 2);
lean_ctor_set(v___x_3289_, 0, v___x_3330_);
v___x_3332_ = v___x_3289_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3334_; 
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 1, v___x_3332_);
lean_ctor_set(v___x_3294_, 0, v___x_3329_);
v___x_3334_ = v___x_3294_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3335_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3336_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3285_);
v___x_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3337_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3334_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3328_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3322_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = l_Lean_Json_mkObj(v___x_3342_);
lean_dec_ref_known(v___x_3342_, 2);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3316_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
lean_ctor_set(v___x_3345_, 1, v___x_3338_);
v___x_3346_ = l_Lean_Json_mkObj(v___x_3345_);
lean_dec_ref_known(v___x_3345_, 2);
v_fst_3061_ = v___x_3346_;
v_snd_3062_ = v_snd_3312_;
goto v___jp_3060_;
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
lean_del_object(v___x_3304_);
lean_dec(v_fst_3301_);
lean_del_object(v___x_3299_);
lean_del_object(v___x_3294_);
lean_dec(v_fst_3291_);
lean_del_object(v___x_3289_);
lean_dec_ref_known(v_e_3000_, 3);
return v___x_3306_;
}
}
}
}
else
{
lean_del_object(v___x_3294_);
lean_dec(v_fst_3291_);
lean_del_object(v___x_3289_);
lean_dec_ref_known(v_e_3000_, 3);
return v___x_3296_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3000_, 3);
return v___x_3286_;
}
}
case 8:
{
lean_object* v_declName_3359_; lean_object* v_type_3360_; lean_object* v_value_3361_; lean_object* v_body_3362_; uint8_t v_nondep_3363_; lean_object* v___x_3364_; 
v_declName_3359_ = lean_ctor_get(v_e_3000_, 0);
v_type_3360_ = lean_ctor_get(v_e_3000_, 1);
v_value_3361_ = lean_ctor_get(v_e_3000_, 2);
v_body_3362_ = lean_ctor_get(v_e_3000_, 3);
v_nondep_3363_ = lean_ctor_get_uint8(v_e_3000_, sizeof(void*)*4 + 8);
lean_inc(v_declName_3359_);
v___x_3364_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3359_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3457_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3457_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3457_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v_fst_3369_; lean_object* v_snd_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3456_; 
v_fst_3369_ = lean_ctor_get(v_a_3365_, 0);
v_snd_3370_ = lean_ctor_get(v_a_3365_, 1);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_a_3365_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3372_ = v_a_3365_;
v_isShared_3373_ = v_isSharedCheck_3456_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_snd_3370_);
lean_inc(v_fst_3369_);
lean_dec(v_a_3365_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3456_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; 
lean_inc_ref(v_type_3360_);
v___x_3374_ = l_LeanExport_dumpExprAux(v_type_3360_, v_a_3001_, v_snd_3370_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3455_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3377_ = v___x_3374_;
v_isShared_3378_ = v_isSharedCheck_3455_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3374_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3455_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v_fst_3379_; lean_object* v_snd_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3454_; 
v_fst_3379_ = lean_ctor_get(v_a_3375_, 0);
v_snd_3380_ = lean_ctor_get(v_a_3375_, 1);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_a_3375_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3382_ = v_a_3375_;
v_isShared_3383_ = v_isSharedCheck_3454_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_snd_3380_);
lean_inc(v_fst_3379_);
lean_dec(v_a_3375_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3454_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; 
lean_inc_ref(v_value_3361_);
v___x_3384_ = l_LeanExport_dumpExprAux(v_value_3361_, v_a_3001_, v_snd_3380_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3453_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3453_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3453_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v_fst_3389_; lean_object* v_snd_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3452_; 
v_fst_3389_ = lean_ctor_get(v_a_3385_, 0);
v_snd_3390_ = lean_ctor_get(v_a_3385_, 1);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_a_3385_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3392_ = v_a_3385_;
v_isShared_3393_ = v_isSharedCheck_3452_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_snd_3390_);
lean_inc(v_fst_3389_);
lean_dec(v_a_3385_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3452_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; 
lean_inc_ref(v_body_3362_);
v___x_3394_ = l_LeanExport_dumpExprAux(v_body_3362_, v_a_3001_, v_snd_3390_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3451_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3451_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3451_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_fst_3399_; lean_object* v_snd_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3450_; 
v_fst_3399_ = lean_ctor_get(v_a_3395_, 0);
v_snd_3400_ = lean_ctor_get(v_a_3395_, 1);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_a_3395_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3402_ = v_a_3395_;
v_isShared_3403_ = v_isSharedCheck_3450_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_snd_3400_);
lean_inc(v_fst_3399_);
lean_dec(v_a_3395_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3450_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v___x_3404_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__12));
v___x_3405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3406_ = l_Lean_JsonNumber_fromNat(v_fst_3369_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 2);
lean_ctor_set(v___x_3397_, 0, v___x_3406_);
v___x_3408_ = v___x_3397_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3410_; 
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 1, v___x_3408_);
lean_ctor_set(v___x_3402_, 0, v___x_3405_);
v___x_3410_ = v___x_3402_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3411_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3412_ = l_Lean_JsonNumber_fromNat(v_fst_3379_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set_tag(v___x_3387_, 2);
lean_ctor_set(v___x_3387_, 0, v___x_3412_);
v___x_3414_ = v___x_3387_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3416_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 1, v___x_3414_);
lean_ctor_set(v___x_3392_, 0, v___x_3411_);
v___x_3416_ = v___x_3392_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3417_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_3418_ = l_Lean_JsonNumber_fromNat(v_fst_3389_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set_tag(v___x_3377_, 2);
lean_ctor_set(v___x_3377_, 0, v___x_3418_);
v___x_3420_ = v___x_3377_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3422_; 
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 1, v___x_3420_);
lean_ctor_set(v___x_3382_, 0, v___x_3417_);
v___x_3422_ = v___x_3382_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
v___x_3423_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3424_ = l_Lean_JsonNumber_fromNat(v_fst_3399_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set_tag(v___x_3367_, 2);
lean_ctor_set(v___x_3367_, 0, v___x_3424_);
v___x_3426_ = v___x_3367_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3428_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 1, v___x_3426_);
lean_ctor_set(v___x_3372_, 0, v___x_3423_);
v___x_3428_ = v___x_3372_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3429_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__14));
v___x_3430_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3430_, 0, v_nondep_3363_);
v___x_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = lean_box(0);
v___x_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3428_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3422_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3416_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3410_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = l_Lean_Json_mkObj(v___x_3437_);
lean_dec_ref_known(v___x_3437_, 2);
v___x_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3404_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
lean_ctor_set(v___x_3440_, 1, v___x_3432_);
v___x_3441_ = l_Lean_Json_mkObj(v___x_3440_);
lean_dec_ref_known(v___x_3440_, 2);
v_fst_3061_ = v___x_3441_;
v_snd_3062_ = v_snd_3400_;
goto v___jp_3060_;
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
lean_del_object(v___x_3392_);
lean_dec(v_fst_3389_);
lean_del_object(v___x_3387_);
lean_del_object(v___x_3382_);
lean_dec(v_fst_3379_);
lean_del_object(v___x_3377_);
lean_del_object(v___x_3372_);
lean_dec(v_fst_3369_);
lean_del_object(v___x_3367_);
lean_dec_ref_known(v_e_3000_, 4);
return v___x_3394_;
}
}
}
}
else
{
lean_del_object(v___x_3382_);
lean_dec(v_fst_3379_);
lean_del_object(v___x_3377_);
lean_del_object(v___x_3372_);
lean_dec(v_fst_3369_);
lean_del_object(v___x_3367_);
lean_dec_ref_known(v_e_3000_, 4);
return v___x_3384_;
}
}
}
}
else
{
lean_del_object(v___x_3372_);
lean_dec(v_fst_3369_);
lean_del_object(v___x_3367_);
lean_dec_ref_known(v_e_3000_, 4);
return v___x_3374_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3000_, 4);
return v___x_3364_;
}
}
case 9:
{
lean_object* v_a_3458_; 
v_a_3458_ = lean_ctor_get(v_e_3000_, 0);
lean_inc_ref(v_a_3458_);
if (lean_obj_tag(v_a_3458_) == 0)
{
lean_object* v_val_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3490_; 
v_val_3459_ = lean_ctor_get(v_a_3458_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_a_3458_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3461_ = v_a_3458_;
v_isShared_3462_ = v_isSharedCheck_3490_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_val_3459_);
lean_dec(v_a_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3490_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; 
v___x_3463_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v_snd_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3480_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref_known(v___x_3463_, 1);
v_snd_3465_ = lean_ctor_get(v_a_3464_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_a_3464_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; 
v_unused_3481_ = lean_ctor_get(v_a_3464_, 0);
lean_dec(v_unused_3481_);
v___x_3467_ = v_a_3464_;
v_isShared_3468_ = v_isSharedCheck_3480_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_snd_3465_);
lean_dec(v_a_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3480_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3469_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__15));
v___x_3470_ = l_Nat_reprFast(v_val_3459_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set_tag(v___x_3461_, 3);
lean_ctor_set(v___x_3461_, 0, v___x_3470_);
v___x_3472_ = v___x_3461_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3474_; 
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v___x_3472_);
lean_ctor_set(v___x_3467_, 0, v___x_3469_);
v___x_3474_ = v___x_3467_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = lean_box(0);
v___x_3476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3474_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = l_Lean_Json_mkObj(v___x_3476_);
lean_dec_ref_known(v___x_3476_, 2);
v_fst_3061_ = v___x_3477_;
v_snd_3062_ = v_snd_3465_;
goto v___jp_3060_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_del_object(v___x_3461_);
lean_dec(v_val_3459_);
lean_dec_ref_known(v_e_3000_, 1);
v_a_3482_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3463_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3463_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
else
{
lean_object* v_val_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3521_; 
v_val_3491_ = lean_ctor_get(v_a_3458_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_a_3458_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3493_ = v_a_3458_;
v_isShared_3494_ = v_isSharedCheck_3521_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_val_3491_);
lean_dec(v_a_3458_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3521_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; 
v___x_3495_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v_snd_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3511_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v_snd_3497_ = lean_ctor_get(v_a_3496_, 1);
v_isSharedCheck_3511_ = !lean_is_exclusive(v_a_3496_);
if (v_isSharedCheck_3511_ == 0)
{
lean_object* v_unused_3512_; 
v_unused_3512_ = lean_ctor_get(v_a_3496_, 0);
lean_dec(v_unused_3512_);
v___x_3499_ = v_a_3496_;
v_isShared_3500_ = v_isSharedCheck_3511_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_snd_3497_);
lean_dec(v_a_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3511_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3501_; lean_object* v___x_3503_; 
v___x_3501_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__16));
if (v_isShared_3494_ == 0)
{
lean_ctor_set_tag(v___x_3493_, 3);
v___x_3503_ = v___x_3493_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_val_3491_);
v___x_3503_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
lean_object* v___x_3505_; 
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 1, v___x_3503_);
lean_ctor_set(v___x_3499_, 0, v___x_3501_);
v___x_3505_ = v___x_3499_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3501_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v___x_3503_);
v___x_3505_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = lean_box(0);
v___x_3507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3505_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = l_Lean_Json_mkObj(v___x_3507_);
lean_dec_ref_known(v___x_3507_, 2);
v_fst_3061_ = v___x_3508_;
v_snd_3062_ = v_snd_3497_;
goto v___jp_3060_;
}
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_del_object(v___x_3493_);
lean_dec_ref(v_val_3491_);
lean_dec_ref_known(v_e_3000_, 1);
v_a_3513_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3495_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3495_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_3522_; lean_object* v_expr_3523_; lean_object* v___x_3524_; 
v_data_3522_ = lean_ctor_get(v_e_3000_, 0);
v_expr_3523_ = lean_ctor_get(v_e_3000_, 1);
lean_inc_ref(v_expr_3523_);
v___x_3524_ = l_LeanExport_dumpExprAux(v_expr_3523_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3554_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3527_ = v___x_3524_;
v_isShared_3528_ = v_isSharedCheck_3554_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3554_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v_fst_3529_; lean_object* v_snd_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3553_; 
v_fst_3529_ = lean_ctor_get(v_a_3525_, 0);
v_snd_3530_ = lean_ctor_get(v_a_3525_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_a_3525_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3532_ = v_a_3525_;
v_isShared_3533_ = v_isSharedCheck_3553_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_snd_3530_);
lean_inc(v_fst_3529_);
lean_dec(v_a_3525_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3553_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v___x_3534_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__17));
v___x_3535_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__18));
lean_inc(v_data_3522_);
v___x_3536_ = l___private_LeanExport_Basic_0__Lean_KVMap_toJson(v_data_3522_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 1, v___x_3536_);
lean_ctor_set(v___x_3532_, 0, v___x_3535_);
v___x_3538_ = v___x_3532_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3535_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3542_; 
v___x_3539_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__19));
v___x_3540_ = l_Lean_JsonNumber_fromNat(v_fst_3529_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set_tag(v___x_3527_, 2);
lean_ctor_set(v___x_3527_, 0, v___x_3540_);
v___x_3542_ = v___x_3527_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3539_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = lean_box(0);
v___x_3545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3543_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3538_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = l_Lean_Json_mkObj(v___x_3546_);
lean_dec_ref_known(v___x_3546_, 2);
v___x_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3534_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v___x_3544_);
v___x_3550_ = l_Lean_Json_mkObj(v___x_3549_);
lean_dec_ref_known(v___x_3549_, 2);
v_fst_3061_ = v___x_3550_;
v_snd_3062_ = v_snd_3530_;
goto v___jp_3060_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3000_, 2);
return v___x_3524_;
}
}
case 11:
{
lean_object* v_typeName_3555_; lean_object* v_idx_3556_; lean_object* v_struct_3557_; lean_object* v___x_3558_; 
v_typeName_3555_ = lean_ctor_get(v_e_3000_, 0);
v_idx_3556_ = lean_ctor_get(v_e_3000_, 1);
v_struct_3557_ = lean_ctor_get(v_e_3000_, 2);
lean_inc(v_typeName_3555_);
v___x_3558_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_typeName_3555_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3610_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3610_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3610_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_fst_3563_; lean_object* v_snd_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3609_; 
v_fst_3563_ = lean_ctor_get(v_a_3559_, 0);
v_snd_3564_ = lean_ctor_get(v_a_3559_, 1);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_a_3559_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3566_ = v_a_3559_;
v_isShared_3567_ = v_isSharedCheck_3609_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_snd_3564_);
lean_inc(v_fst_3563_);
lean_dec(v_a_3559_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3609_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; 
lean_inc_ref(v_struct_3557_);
v___x_3568_ = l_LeanExport_dumpExprAux(v_struct_3557_, v_a_3001_, v_snd_3564_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3608_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3571_ = v___x_3568_;
v_isShared_3572_ = v_isSharedCheck_3608_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3568_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3608_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v_fst_3573_; lean_object* v_snd_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3607_; 
v_fst_3573_ = lean_ctor_get(v_a_3569_, 0);
v_snd_3574_ = lean_ctor_get(v_a_3569_, 1);
v_isSharedCheck_3607_ = !lean_is_exclusive(v_a_3569_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3576_ = v_a_3569_;
v_isShared_3577_ = v_isSharedCheck_3607_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_snd_3574_);
lean_inc(v_fst_3573_);
lean_dec(v_a_3569_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3607_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3582_; 
v___x_3578_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__20));
v___x_3579_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__21));
v___x_3580_ = l_Lean_JsonNumber_fromNat(v_fst_3563_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set_tag(v___x_3571_, 2);
lean_ctor_set(v___x_3571_, 0, v___x_3580_);
v___x_3582_ = v___x_3571_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3584_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3582_);
lean_ctor_set(v___x_3576_, 0, v___x_3579_);
v___x_3584_ = v___x_3576_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3579_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3585_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__22));
lean_inc(v_idx_3556_);
v___x_3586_ = l_Lean_JsonNumber_fromNat(v_idx_3556_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 2);
lean_ctor_set(v___x_3561_, 0, v___x_3586_);
v___x_3588_ = v___x_3561_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3590_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 1, v___x_3588_);
lean_ctor_set(v___x_3566_, 0, v___x_3585_);
v___x_3590_ = v___x_3566_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3591_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__23));
v___x_3592_ = l_Lean_JsonNumber_fromNat(v_fst_3573_);
v___x_3593_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3591_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = lean_box(0);
v___x_3596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3594_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3590_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3584_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = l_Lean_Json_mkObj(v___x_3598_);
lean_dec_ref_known(v___x_3598_, 2);
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3578_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
lean_ctor_set(v___x_3601_, 1, v___x_3595_);
v___x_3602_ = l_Lean_Json_mkObj(v___x_3601_);
lean_dec_ref_known(v___x_3601_, 2);
v_fst_3061_ = v___x_3602_;
v_snd_3062_ = v_snd_3574_;
goto v___jp_3060_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3566_);
lean_dec(v_fst_3563_);
lean_del_object(v___x_3561_);
lean_dec_ref_known(v_e_3000_, 3);
return v___x_3568_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3000_, 3);
return v___x_3558_;
}
}
default: 
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = lean_obj_once(&l_LeanExport_dumpExprAux___closed__26, &l_LeanExport_dumpExprAux___closed__26_once, _init_l_LeanExport_dumpExprAux___closed__26);
v___x_3612_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_3611_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v_fst_3614_; lean_object* v_snd_3615_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
v_fst_3614_ = lean_ctor_get(v_a_3613_, 0);
lean_inc(v_fst_3614_);
v_snd_3615_ = lean_ctor_get(v_a_3613_, 1);
lean_inc(v_snd_3615_);
lean_dec(v_a_3613_);
v_fst_3061_ = v_fst_3614_;
v_snd_3062_ = v_snd_3615_;
goto v___jp_3060_;
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec_ref(v_e_3000_);
v_a_3616_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3612_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3612_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
}
v___jp_3024_:
{
lean_object* v_size_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_size_3035_ = lean_ctor_get(v_visitedExprs_3028_, 0);
lean_inc_n(v_size_3035_, 2);
v___x_3036_ = l_Lean_JsonNumber_fromNat(v_size_3035_);
v___x_3037_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
v___x_3038_ = l_Lean_Json_setObjVal_x21(v_fst_3025_, v___x_3023_, v___x_3037_);
v___x_3039_ = l_Lean_Json_compress(v___x_3038_);
v___x_3040_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_3039_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3050_; 
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3050_ == 0)
{
lean_object* v_unused_3051_; 
v_unused_3051_ = lean_ctor_get(v___x_3040_, 0);
lean_dec(v_unused_3051_);
v___x_3042_ = v___x_3040_;
v_isShared_3043_ = v_isSharedCheck_3050_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v___x_3040_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3050_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
lean_inc(v_size_3035_);
v___x_3044_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_visitedExprs_3028_, v_e_3000_, v_size_3035_);
v___x_3045_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_3045_, 0, v_visitedNames_3026_);
lean_ctor_set(v___x_3045_, 1, v_visitedLevels_3027_);
lean_ctor_set(v___x_3045_, 2, v___x_3044_);
lean_ctor_set(v___x_3045_, 3, v_visitedConstants_3029_);
lean_ctor_set(v___x_3045_, 4, v_noMDataExprs_3030_);
lean_ctor_set(v___x_3045_, 5, v_recursorMap_3034_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*6, v_exportMData_3031_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*6 + 1, v_exportUnsafe_3032_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*6 + 2, v_ignoreMissing_3033_);
v___x_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3046_, 0, v_size_3035_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3046_);
v___x_3048_ = v___x_3042_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec(v_size_3035_);
lean_dec(v_recursorMap_3034_);
lean_dec_ref(v_noMDataExprs_3030_);
lean_dec_ref(v_visitedConstants_3029_);
lean_dec_ref(v_visitedExprs_3028_);
lean_dec_ref(v_visitedLevels_3027_);
lean_dec_ref(v_visitedNames_3026_);
lean_dec_ref(v_e_3000_);
v_a_3052_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3040_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3040_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
v___jp_3060_:
{
lean_object* v_visitedNames_3063_; lean_object* v_visitedLevels_3064_; lean_object* v_visitedExprs_3065_; lean_object* v_visitedConstants_3066_; lean_object* v_noMDataExprs_3067_; uint8_t v_exportMData_3068_; uint8_t v_exportUnsafe_3069_; uint8_t v_ignoreMissing_3070_; lean_object* v_recursorMap_3071_; 
v_visitedNames_3063_ = lean_ctor_get(v_snd_3062_, 0);
lean_inc_ref(v_visitedNames_3063_);
v_visitedLevels_3064_ = lean_ctor_get(v_snd_3062_, 1);
lean_inc_ref(v_visitedLevels_3064_);
v_visitedExprs_3065_ = lean_ctor_get(v_snd_3062_, 2);
lean_inc_ref(v_visitedExprs_3065_);
v_visitedConstants_3066_ = lean_ctor_get(v_snd_3062_, 3);
lean_inc_ref(v_visitedConstants_3066_);
v_noMDataExprs_3067_ = lean_ctor_get(v_snd_3062_, 4);
lean_inc_ref(v_noMDataExprs_3067_);
v_exportMData_3068_ = lean_ctor_get_uint8(v_snd_3062_, sizeof(void*)*6);
v_exportUnsafe_3069_ = lean_ctor_get_uint8(v_snd_3062_, sizeof(void*)*6 + 1);
v_ignoreMissing_3070_ = lean_ctor_get_uint8(v_snd_3062_, sizeof(void*)*6 + 2);
v_recursorMap_3071_ = lean_ctor_get(v_snd_3062_, 5);
lean_inc(v_recursorMap_3071_);
lean_dec_ref(v_snd_3062_);
v_fst_3025_ = v_fst_3061_;
v_visitedNames_3026_ = v_visitedNames_3063_;
v_visitedLevels_3027_ = v_visitedLevels_3064_;
v_visitedExprs_3028_ = v_visitedExprs_3065_;
v_visitedConstants_3029_ = v_visitedConstants_3066_;
v_noMDataExprs_3030_ = v_noMDataExprs_3067_;
v_exportMData_3031_ = v_exportMData_3068_;
v_exportUnsafe_3032_ = v_exportUnsafe_3069_;
v_ignoreMissing_3033_ = v_ignoreMissing_3070_;
v_recursorMap_3034_ = v_recursorMap_3071_;
goto v___jp_3024_;
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr(lean_object* v_e_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
uint8_t v_exportMData_3628_; 
v_exportMData_3628_ = lean_ctor_get_uint8(v_a_3626_, sizeof(void*)*6);
if (v_exportMData_3628_ == 0)
{
lean_object* v_visitedNames_3629_; lean_object* v_visitedLevels_3630_; lean_object* v_visitedExprs_3631_; lean_object* v_visitedConstants_3632_; uint8_t v_exportUnsafe_3633_; uint8_t v_ignoreMissing_3634_; lean_object* v_recursorMap_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3656_; 
v_visitedNames_3629_ = lean_ctor_get(v_a_3626_, 0);
v_visitedLevels_3630_ = lean_ctor_get(v_a_3626_, 1);
v_visitedExprs_3631_ = lean_ctor_get(v_a_3626_, 2);
v_visitedConstants_3632_ = lean_ctor_get(v_a_3626_, 3);
v_exportUnsafe_3633_ = lean_ctor_get_uint8(v_a_3626_, sizeof(void*)*6 + 1);
v_ignoreMissing_3634_ = lean_ctor_get_uint8(v_a_3626_, sizeof(void*)*6 + 2);
v_recursorMap_3635_ = lean_ctor_get(v_a_3626_, 5);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_a_3626_);
if (v_isSharedCheck_3656_ == 0)
{
lean_object* v_unused_3657_; 
v_unused_3657_ = lean_ctor_get(v_a_3626_, 4);
lean_dec(v_unused_3657_);
v___x_3637_ = v_a_3626_;
v_isShared_3638_ = v_isSharedCheck_3656_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_recursorMap_3635_);
lean_inc(v_visitedConstants_3632_);
lean_inc(v_visitedExprs_3631_);
lean_inc(v_visitedLevels_3630_);
lean_inc(v_visitedNames_3629_);
lean_dec(v_a_3626_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3656_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3639_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 4, v___x_3639_);
v___x_3641_ = v___x_3637_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_visitedNames_3629_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_visitedLevels_3630_);
lean_ctor_set(v_reuseFailAlloc_3655_, 2, v_visitedExprs_3631_);
lean_ctor_set(v_reuseFailAlloc_3655_, 3, v_visitedConstants_3632_);
lean_ctor_set(v_reuseFailAlloc_3655_, 4, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3655_, 5, v_recursorMap_3635_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*6, v_exportMData_3628_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*6 + 1, v_exportUnsafe_3633_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*6 + 2, v_ignoreMissing_3634_);
v___x_3641_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; 
v___x_3642_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_3624_, v_a_3625_, v___x_3641_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v_fst_3644_; lean_object* v_snd_3645_; lean_object* v___x_3646_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___x_3642_, 1);
v_fst_3644_ = lean_ctor_get(v_a_3643_, 0);
lean_inc(v_fst_3644_);
v_snd_3645_ = lean_ctor_get(v_a_3643_, 1);
lean_inc(v_snd_3645_);
lean_dec(v_a_3643_);
v___x_3646_ = l_LeanExport_dumpExprAux(v_fst_3644_, v_a_3625_, v_snd_3645_);
return v___x_3646_;
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
v_a_3647_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3642_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3642_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
}
}
else
{
lean_object* v___x_3658_; 
v___x_3658_ = l_LeanExport_dumpExprAux(v_e_3624_, v_a_3625_, v_a_3626_);
return v___x_3658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t v_sz_3668_, size_t v_i_3669_, lean_object* v_bs_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v___x_3674_; 
v___x_3674_ = lean_usize_dec_lt(v_i_3669_, v_sz_3668_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3675_, 0, v_bs_3670_);
lean_ctor_set(v___x_3675_, 1, v___y_3672_);
v___x_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
return v___x_3676_;
}
else
{
lean_object* v_v_3677_; lean_object* v_toConstantVal_3678_; lean_object* v_numParams_3679_; lean_object* v_numIndices_3680_; lean_object* v_all_3681_; lean_object* v_ctors_3682_; lean_object* v_numNested_3683_; uint8_t v_isRec_3684_; uint8_t v_isUnsafe_3685_; uint8_t v_isReflexive_3686_; lean_object* v_name_3687_; lean_object* v_levelParams_3688_; lean_object* v_type_3689_; lean_object* v___x_3690_; 
v_v_3677_ = lean_array_uget_borrowed(v_bs_3670_, v_i_3669_);
v_toConstantVal_3678_ = lean_ctor_get(v_v_3677_, 0);
v_numParams_3679_ = lean_ctor_get(v_v_3677_, 1);
lean_inc(v_numParams_3679_);
v_numIndices_3680_ = lean_ctor_get(v_v_3677_, 2);
lean_inc(v_numIndices_3680_);
v_all_3681_ = lean_ctor_get(v_v_3677_, 3);
lean_inc(v_all_3681_);
v_ctors_3682_ = lean_ctor_get(v_v_3677_, 4);
lean_inc(v_ctors_3682_);
v_numNested_3683_ = lean_ctor_get(v_v_3677_, 5);
lean_inc(v_numNested_3683_);
v_isRec_3684_ = lean_ctor_get_uint8(v_v_3677_, sizeof(void*)*6);
v_isUnsafe_3685_ = lean_ctor_get_uint8(v_v_3677_, sizeof(void*)*6 + 1);
v_isReflexive_3686_ = lean_ctor_get_uint8(v_v_3677_, sizeof(void*)*6 + 2);
v_name_3687_ = lean_ctor_get(v_toConstantVal_3678_, 0);
v_levelParams_3688_ = lean_ctor_get(v_toConstantVal_3678_, 1);
lean_inc(v_levelParams_3688_);
v_type_3689_ = lean_ctor_get(v_toConstantVal_3678_, 2);
lean_inc_ref(v_type_3689_);
lean_inc(v_name_3687_);
v___x_3690_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3687_, v___y_3671_, v___y_3672_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v_fst_3692_; lean_object* v_snd_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3835_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3690_, 1);
v_fst_3692_ = lean_ctor_get(v_a_3691_, 0);
v_snd_3693_ = lean_ctor_get(v_a_3691_, 1);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_a_3691_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3695_ = v_a_3691_;
v_isShared_3696_ = v_isSharedCheck_3835_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_snd_3693_);
lean_inc(v_fst_3692_);
lean_dec(v_a_3691_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3835_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; lean_object* v_bs_x27_3698_; lean_object* v_fst_3700_; lean_object* v_snd_3701_; lean_object* v___y_3707_; lean_object* v___x_3719_; 
v___x_3697_ = lean_unsigned_to_nat(0u);
v_bs_x27_3698_ = lean_array_uset(v_bs_3670_, v_i_3669_, v___x_3697_);
v___x_3719_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3688_, v___y_3671_, v_snd_3693_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3834_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3722_ = v___x_3719_;
v_isShared_3723_ = v_isSharedCheck_3834_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3834_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v_fst_3724_; lean_object* v_snd_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3833_; 
v_fst_3724_ = lean_ctor_get(v_a_3720_, 0);
v_snd_3725_ = lean_ctor_get(v_a_3720_, 1);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_a_3720_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3727_ = v_a_3720_;
v_isShared_3728_ = v_isSharedCheck_3833_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_snd_3725_);
lean_inc(v_fst_3724_);
lean_dec(v_a_3720_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3833_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_LeanExport_dumpExpr(v_type_3689_, v___y_3671_, v_snd_3725_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v_fst_3731_; lean_object* v_snd_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3824_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v_fst_3731_ = lean_ctor_get(v_a_3730_, 0);
v_snd_3732_ = lean_ctor_get(v_a_3730_, 1);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_a_3730_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3734_ = v_a_3730_;
v_isShared_3735_ = v_isSharedCheck_3824_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_snd_3732_);
lean_inc(v_fst_3731_);
lean_dec(v_a_3730_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3824_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3736_; 
v___x_3736_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_3681_, v___y_3671_, v_snd_3732_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3823_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3823_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3823_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v_fst_3741_; lean_object* v_snd_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3822_; 
v_fst_3741_ = lean_ctor_get(v_a_3737_, 0);
v_snd_3742_ = lean_ctor_get(v_a_3737_, 1);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_a_3737_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3744_ = v_a_3737_;
v_isShared_3745_ = v_isSharedCheck_3822_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_snd_3742_);
lean_inc(v_fst_3741_);
lean_dec(v_a_3737_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3822_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3746_; 
v___x_3746_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_ctors_3682_, v___y_3671_, v_snd_3742_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3821_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3749_ = v___x_3746_;
v_isShared_3750_ = v_isSharedCheck_3821_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3746_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3821_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v_fst_3751_; lean_object* v_snd_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3820_; 
v_fst_3751_ = lean_ctor_get(v_a_3747_, 0);
v_snd_3752_ = lean_ctor_get(v_a_3747_, 1);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_a_3747_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3754_ = v_a_3747_;
v_isShared_3755_ = v_isSharedCheck_3820_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_snd_3752_);
lean_inc(v_fst_3751_);
lean_dec(v_a_3747_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3820_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3759_; 
v___x_3756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3757_ = l_Lean_JsonNumber_fromNat(v_fst_3692_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set_tag(v___x_3749_, 2);
lean_ctor_set(v___x_3749_, 0, v___x_3757_);
v___x_3759_ = v___x_3749_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3761_; 
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 1, v___x_3759_);
lean_ctor_set(v___x_3754_, 0, v___x_3756_);
v___x_3761_ = v___x_3754_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
lean_object* v___x_3762_; lean_object* v___x_3764_; 
v___x_3762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 1, v_fst_3724_);
lean_ctor_set(v___x_3744_, 0, v___x_3762_);
v___x_3764_ = v___x_3744_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3762_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_fst_3724_);
v___x_3764_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3765_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3766_ = l_Lean_JsonNumber_fromNat(v_fst_3731_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set_tag(v___x_3739_, 2);
lean_ctor_set(v___x_3739_, 0, v___x_3766_);
v___x_3768_ = v___x_3739_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3770_; 
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 1, v___x_3768_);
lean_ctor_set(v___x_3734_, 0, v___x_3765_);
v___x_3770_ = v___x_3734_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3774_; 
v___x_3771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4));
v___x_3772_ = l_Lean_JsonNumber_fromNat(v_numParams_3679_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set_tag(v___x_3722_, 2);
lean_ctor_set(v___x_3722_, 0, v___x_3772_);
v___x_3774_ = v___x_3722_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3776_; 
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 1, v___x_3774_);
lean_ctor_set(v___x_3727_, 0, v___x_3771_);
v___x_3776_ = v___x_3727_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3781_; 
v___x_3777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0));
v___x_3778_ = l_Lean_JsonNumber_fromNat(v_numIndices_3680_);
v___x_3779_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 1, v___x_3779_);
lean_ctor_set(v___x_3695_, 0, v___x_3777_);
v___x_3781_ = v___x_3695_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v___x_3779_);
v___x_3781_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
v___x_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
lean_ctor_set(v___x_3783_, 1, v_fst_3741_);
v___x_3784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2));
v___x_3785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
lean_ctor_set(v___x_3785_, 1, v_fst_3751_);
v___x_3786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3));
v___x_3787_ = l_Lean_JsonNumber_fromNat(v_numNested_3683_);
v___x_3788_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
v___x_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3786_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__4));
v___x_3791_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3791_, 0, v_isRec_3684_);
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__5));
v___x_3794_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3794_, 0, v_isReflexive_3686_);
v___x_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6));
v___x_3797_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3797_, 0, v_isUnsafe_3685_);
v___x_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3796_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___x_3799_ = lean_box(0);
v___x_3800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3795_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3792_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3789_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3785_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
v___x_3805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3783_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3781_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3776_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3770_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3764_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3761_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = l_Lean_Json_mkObj(v___x_3810_);
lean_dec_ref_known(v___x_3810_, 2);
v_fst_3700_ = v___x_3811_;
v_snd_3701_ = v_snd_3752_;
goto v___jp_3699_;
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
lean_del_object(v___x_3744_);
lean_dec(v_fst_3741_);
lean_del_object(v___x_3739_);
lean_del_object(v___x_3734_);
lean_dec(v_fst_3731_);
lean_del_object(v___x_3727_);
lean_dec(v_fst_3724_);
lean_del_object(v___x_3722_);
lean_del_object(v___x_3695_);
lean_dec(v_fst_3692_);
lean_dec(v_numNested_3683_);
lean_dec(v_numIndices_3680_);
lean_dec(v_numParams_3679_);
v___y_3707_ = v___x_3746_;
goto v___jp_3706_;
}
}
}
}
else
{
lean_del_object(v___x_3734_);
lean_dec(v_fst_3731_);
lean_del_object(v___x_3727_);
lean_dec(v_fst_3724_);
lean_del_object(v___x_3722_);
lean_del_object(v___x_3695_);
lean_dec(v_fst_3692_);
lean_dec(v_numNested_3683_);
lean_dec(v_ctors_3682_);
lean_dec(v_numIndices_3680_);
lean_dec(v_numParams_3679_);
v___y_3707_ = v___x_3736_;
goto v___jp_3706_;
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_del_object(v___x_3727_);
lean_dec(v_fst_3724_);
lean_del_object(v___x_3722_);
lean_dec_ref(v_bs_x27_3698_);
lean_del_object(v___x_3695_);
lean_dec(v_fst_3692_);
lean_dec(v_numNested_3683_);
lean_dec(v_ctors_3682_);
lean_dec(v_all_3681_);
lean_dec(v_numIndices_3680_);
lean_dec(v_numParams_3679_);
v_a_3825_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3729_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3729_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_3695_);
lean_dec(v_fst_3692_);
lean_dec_ref(v_type_3689_);
lean_dec(v_numNested_3683_);
lean_dec(v_ctors_3682_);
lean_dec(v_all_3681_);
lean_dec(v_numIndices_3680_);
lean_dec(v_numParams_3679_);
v___y_3707_ = v___x_3719_;
goto v___jp_3706_;
}
v___jp_3699_:
{
size_t v___x_3702_; size_t v___x_3703_; lean_object* v___x_3704_; 
v___x_3702_ = ((size_t)1ULL);
v___x_3703_ = lean_usize_add(v_i_3669_, v___x_3702_);
v___x_3704_ = lean_array_uset(v_bs_x27_3698_, v_i_3669_, v_fst_3700_);
v_i_3669_ = v___x_3703_;
v_bs_3670_ = v___x_3704_;
v___y_3672_ = v_snd_3701_;
goto _start;
}
v___jp_3706_:
{
if (lean_obj_tag(v___y_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v_fst_3709_; lean_object* v_snd_3710_; 
v_a_3708_ = lean_ctor_get(v___y_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___y_3707_, 1);
v_fst_3709_ = lean_ctor_get(v_a_3708_, 0);
lean_inc(v_fst_3709_);
v_snd_3710_ = lean_ctor_get(v_a_3708_, 1);
lean_inc(v_snd_3710_);
lean_dec(v_a_3708_);
v_fst_3700_ = v_fst_3709_;
v_snd_3701_ = v_snd_3710_;
goto v___jp_3699_;
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec_ref(v_bs_x27_3698_);
v_a_3711_ = lean_ctor_get(v___y_3707_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___y_3707_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___y_3707_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___y_3707_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec_ref(v_type_3689_);
lean_dec(v_levelParams_3688_);
lean_dec(v_numNested_3683_);
lean_dec(v_ctors_3682_);
lean_dec(v_all_3681_);
lean_dec(v_numIndices_3680_);
lean_dec(v_numParams_3679_);
lean_dec_ref(v_bs_3670_);
v_a_3836_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3690_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3690_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19(size_t v_sz_3847_, size_t v_i_3848_, lean_object* v_bs_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
uint8_t v___x_3853_; 
v___x_3853_ = lean_usize_dec_lt(v_i_3848_, v_sz_3847_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3854_, 0, v_bs_3849_);
lean_ctor_set(v___x_3854_, 1, v___y_3851_);
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
return v___x_3855_;
}
else
{
lean_object* v_v_3856_; lean_object* v_toConstantVal_3857_; lean_object* v_induct_3858_; lean_object* v_cidx_3859_; lean_object* v_numParams_3860_; lean_object* v_numFields_3861_; uint8_t v_isUnsafe_3862_; lean_object* v_name_3863_; lean_object* v_levelParams_3864_; lean_object* v_type_3865_; lean_object* v___x_3866_; 
v_v_3856_ = lean_array_uget_borrowed(v_bs_3849_, v_i_3848_);
v_toConstantVal_3857_ = lean_ctor_get(v_v_3856_, 0);
v_induct_3858_ = lean_ctor_get(v_v_3856_, 1);
lean_inc(v_induct_3858_);
v_cidx_3859_ = lean_ctor_get(v_v_3856_, 2);
lean_inc(v_cidx_3859_);
v_numParams_3860_ = lean_ctor_get(v_v_3856_, 3);
lean_inc(v_numParams_3860_);
v_numFields_3861_ = lean_ctor_get(v_v_3856_, 4);
lean_inc(v_numFields_3861_);
v_isUnsafe_3862_ = lean_ctor_get_uint8(v_v_3856_, sizeof(void*)*5);
v_name_3863_ = lean_ctor_get(v_toConstantVal_3857_, 0);
v_levelParams_3864_ = lean_ctor_get(v_toConstantVal_3857_, 1);
lean_inc(v_levelParams_3864_);
v_type_3865_ = lean_ctor_get(v_toConstantVal_3857_, 2);
lean_inc_ref(v_type_3865_);
lean_inc(v_name_3863_);
v___x_3866_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3863_, v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v_fst_3868_; lean_object* v_snd_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3980_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3866_, 1);
v_fst_3868_ = lean_ctor_get(v_a_3867_, 0);
v_snd_3869_ = lean_ctor_get(v_a_3867_, 1);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_a_3867_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3871_ = v_a_3867_;
v_isShared_3872_ = v_isSharedCheck_3980_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_snd_3869_);
lean_inc(v_fst_3868_);
lean_dec(v_a_3867_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3980_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v_bs_x27_3874_; lean_object* v_fst_3876_; lean_object* v_snd_3877_; lean_object* v___x_3882_; 
v___x_3873_ = lean_unsigned_to_nat(0u);
v_bs_x27_3874_ = lean_array_uset(v_bs_3849_, v_i_3848_, v___x_3873_);
v___x_3882_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3864_, v___y_3850_, v_snd_3869_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v_fst_3884_; lean_object* v_snd_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3968_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
v_fst_3884_ = lean_ctor_get(v_a_3883_, 0);
v_snd_3885_ = lean_ctor_get(v_a_3883_, 1);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_a_3883_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3887_ = v_a_3883_;
v_isShared_3888_ = v_isSharedCheck_3968_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_snd_3885_);
lean_inc(v_fst_3884_);
lean_dec(v_a_3883_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3968_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_LeanExport_dumpExpr(v_type_3865_, v___y_3850_, v_snd_3885_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v_fst_3891_; lean_object* v_snd_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3959_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3889_, 1);
v_fst_3891_ = lean_ctor_get(v_a_3890_, 0);
v_snd_3892_ = lean_ctor_get(v_a_3890_, 1);
v_isSharedCheck_3959_ = !lean_is_exclusive(v_a_3890_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3894_ = v_a_3890_;
v_isShared_3895_ = v_isSharedCheck_3959_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_snd_3892_);
lean_inc(v_fst_3891_);
lean_dec(v_a_3890_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3959_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3896_; 
v___x_3896_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_induct_3858_, v___y_3850_, v_snd_3892_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v_fst_3898_; lean_object* v_snd_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3950_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3896_, 1);
v_fst_3898_ = lean_ctor_get(v_a_3897_, 0);
v_snd_3899_ = lean_ctor_get(v_a_3897_, 1);
v_isSharedCheck_3950_ = !lean_is_exclusive(v_a_3897_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3901_ = v_a_3897_;
v_isShared_3902_ = v_isSharedCheck_3950_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_snd_3899_);
lean_inc(v_fst_3898_);
lean_dec(v_a_3897_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3950_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3904_ = l_Lean_JsonNumber_fromNat(v_fst_3868_);
v___x_3905_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 1, v___x_3905_);
lean_ctor_set(v___x_3901_, 0, v___x_3903_);
v___x_3907_ = v___x_3901_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3908_; lean_object* v___x_3910_; 
v___x_3908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 1, v_fst_3884_);
lean_ctor_set(v___x_3894_, 0, v___x_3908_);
v___x_3910_ = v___x_3894_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_fst_3884_);
v___x_3910_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3915_; 
v___x_3911_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3912_ = l_Lean_JsonNumber_fromNat(v_fst_3891_);
v___x_3913_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 1, v___x_3913_);
lean_ctor_set(v___x_3887_, 0, v___x_3911_);
v___x_3915_ = v___x_3887_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__2));
v___x_3917_ = l_Lean_JsonNumber_fromNat(v_fst_3898_);
v___x_3918_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 1, v___x_3918_);
lean_ctor_set(v___x_3871_, 0, v___x_3916_);
v___x_3920_ = v___x_3871_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__3));
v___x_3922_ = l_Lean_JsonNumber_fromNat(v_cidx_3859_);
v___x_3923_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3921_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4));
v___x_3926_ = l_Lean_JsonNumber_fromNat(v_numParams_3860_);
v___x_3927_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
v___x_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3925_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
v___x_3929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__5));
v___x_3930_ = l_Lean_JsonNumber_fromNat(v_numFields_3861_);
v___x_3931_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
v___x_3932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3929_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
v___x_3933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6));
v___x_3934_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3934_, 0, v_isUnsafe_3862_);
v___x_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3933_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = lean_box(0);
v___x_3937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3935_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3932_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
v___x_3939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3928_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3924_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
v___x_3941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3920_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3915_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3910_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3907_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
v___x_3945_ = l_Lean_Json_mkObj(v___x_3944_);
lean_dec_ref_known(v___x_3944_, 2);
v_fst_3876_ = v___x_3945_;
v_snd_3877_ = v_snd_3899_;
goto v___jp_3875_;
}
}
}
}
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_del_object(v___x_3894_);
lean_dec(v_fst_3891_);
lean_del_object(v___x_3887_);
lean_dec(v_fst_3884_);
lean_dec_ref(v_bs_x27_3874_);
lean_del_object(v___x_3871_);
lean_dec(v_fst_3868_);
lean_dec(v_numFields_3861_);
lean_dec(v_numParams_3860_);
lean_dec(v_cidx_3859_);
v_a_3951_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3896_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3896_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_del_object(v___x_3887_);
lean_dec(v_fst_3884_);
lean_dec_ref(v_bs_x27_3874_);
lean_del_object(v___x_3871_);
lean_dec(v_fst_3868_);
lean_dec(v_numFields_3861_);
lean_dec(v_numParams_3860_);
lean_dec(v_cidx_3859_);
lean_dec(v_induct_3858_);
v_a_3960_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3889_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3889_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
}
else
{
lean_del_object(v___x_3871_);
lean_dec(v_fst_3868_);
lean_dec_ref(v_type_3865_);
lean_dec(v_numFields_3861_);
lean_dec(v_numParams_3860_);
lean_dec(v_cidx_3859_);
lean_dec(v_induct_3858_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3969_; lean_object* v_fst_3970_; lean_object* v_snd_3971_; 
v_a_3969_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3969_);
lean_dec_ref_known(v___x_3882_, 1);
v_fst_3970_ = lean_ctor_get(v_a_3969_, 0);
lean_inc(v_fst_3970_);
v_snd_3971_ = lean_ctor_get(v_a_3969_, 1);
lean_inc(v_snd_3971_);
lean_dec(v_a_3969_);
v_fst_3876_ = v_fst_3970_;
v_snd_3877_ = v_snd_3971_;
goto v___jp_3875_;
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec_ref(v_bs_x27_3874_);
v_a_3972_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3882_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3882_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
v___jp_3875_:
{
size_t v___x_3878_; size_t v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = ((size_t)1ULL);
v___x_3879_ = lean_usize_add(v_i_3848_, v___x_3878_);
v___x_3880_ = lean_array_uset(v_bs_x27_3874_, v_i_3848_, v_fst_3876_);
v_i_3848_ = v___x_3879_;
v_bs_3849_ = v___x_3880_;
v___y_3851_ = v_snd_3877_;
goto _start;
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec_ref(v_type_3865_);
lean_dec(v_levelParams_3864_);
lean_dec(v_numFields_3861_);
lean_dec(v_numParams_3860_);
lean_dec(v_cidx_3859_);
lean_dec(v_induct_3858_);
lean_dec_ref(v_bs_3849_);
v_a_3981_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3866_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3866_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object* v_rule_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v_ctor_3995_; lean_object* v_nfields_3996_; lean_object* v_rhs_3997_; lean_object* v___x_3998_; 
v_ctor_3995_ = lean_ctor_get(v_rule_3991_, 0);
lean_inc(v_ctor_3995_);
v_nfields_3996_ = lean_ctor_get(v_rule_3991_, 1);
lean_inc(v_nfields_3996_);
v_rhs_3997_ = lean_ctor_get(v_rule_3991_, 2);
lean_inc_ref(v_rhs_3997_);
lean_dec_ref(v_rule_3991_);
v___x_3998_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_ctor_3995_, v_a_3992_, v_a_3993_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v_fst_4000_; lean_object* v_snd_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4050_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v_fst_4000_ = lean_ctor_get(v_a_3999_, 0);
v_snd_4001_ = lean_ctor_get(v_a_3999_, 1);
v_isSharedCheck_4050_ = !lean_is_exclusive(v_a_3999_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4003_ = v_a_3999_;
v_isShared_4004_ = v_isSharedCheck_4050_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_snd_4001_);
lean_inc(v_fst_4000_);
lean_dec(v_a_3999_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4050_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4005_; 
v___x_4005_ = l_LeanExport_dumpExpr(v_rhs_3997_, v_a_3992_, v_snd_4001_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4041_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4041_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4041_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v_fst_4010_; lean_object* v_snd_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4040_; 
v_fst_4010_ = lean_ctor_get(v_a_4006_, 0);
v_snd_4011_ = lean_ctor_get(v_a_4006_, 1);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_a_4006_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4013_ = v_a_4006_;
v_isShared_4014_ = v_isSharedCheck_4040_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_snd_4011_);
lean_inc(v_fst_4010_);
lean_dec(v_a_4006_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4040_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4019_; 
v___x_4015_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2));
v___x_4016_ = l_Lean_JsonNumber_fromNat(v_fst_4000_);
v___x_4017_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 1, v___x_4017_);
lean_ctor_set(v___x_4013_, 0, v___x_4015_);
v___x_4019_ = v___x_4013_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4015_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v___x_4017_);
v___x_4019_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4020_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0));
v___x_4021_ = l_Lean_JsonNumber_fromNat(v_nfields_3996_);
v___x_4022_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 1, v___x_4022_);
lean_ctor_set(v___x_4003_, 0, v___x_4020_);
v___x_4024_ = v___x_4003_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4020_);
lean_ctor_set(v_reuseFailAlloc_4038_, 1, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4025_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1));
v___x_4026_ = l_Lean_JsonNumber_fromNat(v_fst_4010_);
v___x_4027_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
v___x_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4025_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
v___x_4029_ = lean_box(0);
v___x_4030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4028_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
v___x_4031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4024_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4019_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = l_Lean_Json_mkObj(v___x_4032_);
lean_dec_ref_known(v___x_4032_, 2);
v___x_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
lean_ctor_set(v___x_4034_, 1, v_snd_4011_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v___x_4034_);
v___x_4036_ = v___x_4008_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_del_object(v___x_4003_);
lean_dec(v_fst_4000_);
lean_dec(v_nfields_3996_);
v_a_4042_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4005_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4005_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec_ref(v_rhs_3997_);
lean_dec(v_nfields_3996_);
v_a_4051_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_3998_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_3998_);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object* v_x_4059_, lean_object* v_x_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
if (lean_obj_tag(v_x_4059_) == 0)
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4064_ = l_List_reverse___redArg(v_x_4060_);
v___x_4065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
lean_ctor_set(v___x_4065_, 1, v___y_4062_);
v___x_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
return v___x_4066_;
}
else
{
lean_object* v_head_4067_; lean_object* v_tail_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4088_; 
v_head_4067_ = lean_ctor_get(v_x_4059_, 0);
v_tail_4068_ = lean_ctor_get(v_x_4059_, 1);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_x_4059_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4070_ = v_x_4059_;
v_isShared_4071_ = v_isSharedCheck_4088_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_tail_4068_);
lean_inc(v_head_4067_);
lean_dec(v_x_4059_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4088_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4072_; 
v___x_4072_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_head_4067_, v___y_4061_, v___y_4062_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v_fst_4074_; lean_object* v_snd_4075_; lean_object* v___x_4077_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4073_);
lean_dec_ref_known(v___x_4072_, 1);
v_fst_4074_ = lean_ctor_get(v_a_4073_, 0);
lean_inc(v_fst_4074_);
v_snd_4075_ = lean_ctor_get(v_a_4073_, 1);
lean_inc(v_snd_4075_);
lean_dec(v_a_4073_);
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 1, v_x_4060_);
lean_ctor_set(v___x_4070_, 0, v_fst_4074_);
v___x_4077_ = v___x_4070_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_fst_4074_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_x_4060_);
v___x_4077_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
v_x_4059_ = v_tail_4068_;
v_x_4060_ = v___x_4077_;
v___y_4062_ = v_snd_4075_;
goto _start;
}
}
else
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
lean_del_object(v___x_4070_);
lean_dec(v_tail_4068_);
lean_dec(v_x_4060_);
v_a_4080_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4082_ = v___x_4072_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4072_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20(size_t v_sz_4093_, size_t v_i_4094_, lean_object* v_bs_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
uint8_t v___x_4099_; 
v___x_4099_ = lean_usize_dec_lt(v_i_4094_, v_sz_4093_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4100_, 0, v_bs_4095_);
lean_ctor_set(v___x_4100_, 1, v___y_4097_);
v___x_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4100_);
return v___x_4101_;
}
else
{
lean_object* v_v_4102_; lean_object* v_toConstantVal_4103_; lean_object* v_all_4104_; lean_object* v_numParams_4105_; lean_object* v_numIndices_4106_; lean_object* v_numMotives_4107_; lean_object* v_numMinors_4108_; lean_object* v_rules_4109_; uint8_t v_k_4110_; uint8_t v_isUnsafe_4111_; lean_object* v_name_4112_; lean_object* v_levelParams_4113_; lean_object* v_type_4114_; lean_object* v___x_4115_; 
v_v_4102_ = lean_array_uget_borrowed(v_bs_4095_, v_i_4094_);
v_toConstantVal_4103_ = lean_ctor_get(v_v_4102_, 0);
v_all_4104_ = lean_ctor_get(v_v_4102_, 1);
lean_inc(v_all_4104_);
v_numParams_4105_ = lean_ctor_get(v_v_4102_, 2);
lean_inc(v_numParams_4105_);
v_numIndices_4106_ = lean_ctor_get(v_v_4102_, 3);
lean_inc(v_numIndices_4106_);
v_numMotives_4107_ = lean_ctor_get(v_v_4102_, 4);
lean_inc(v_numMotives_4107_);
v_numMinors_4108_ = lean_ctor_get(v_v_4102_, 5);
lean_inc(v_numMinors_4108_);
v_rules_4109_ = lean_ctor_get(v_v_4102_, 6);
lean_inc(v_rules_4109_);
v_k_4110_ = lean_ctor_get_uint8(v_v_4102_, sizeof(void*)*7);
v_isUnsafe_4111_ = lean_ctor_get_uint8(v_v_4102_, sizeof(void*)*7 + 1);
v_name_4112_ = lean_ctor_get(v_toConstantVal_4103_, 0);
v_levelParams_4113_ = lean_ctor_get(v_toConstantVal_4103_, 1);
lean_inc(v_levelParams_4113_);
v_type_4114_ = lean_ctor_get(v_toConstantVal_4103_, 2);
lean_inc_ref(v_type_4114_);
lean_inc(v_name_4112_);
v___x_4115_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4112_, v___y_4096_, v___y_4097_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v_fst_4117_; lean_object* v_snd_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4264_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_a_4116_);
lean_dec_ref_known(v___x_4115_, 1);
v_fst_4117_ = lean_ctor_get(v_a_4116_, 0);
v_snd_4118_ = lean_ctor_get(v_a_4116_, 1);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_a_4116_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4120_ = v_a_4116_;
v_isShared_4121_ = v_isSharedCheck_4264_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_snd_4118_);
lean_inc(v_fst_4117_);
lean_dec(v_a_4116_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4264_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4122_; lean_object* v_bs_x27_4123_; lean_object* v_fst_4125_; lean_object* v_snd_4126_; lean_object* v___y_4132_; lean_object* v___x_4144_; 
v___x_4122_ = lean_unsigned_to_nat(0u);
v_bs_x27_4123_ = lean_array_uset(v_bs_4095_, v_i_4094_, v___x_4122_);
v___x_4144_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4113_, v___y_4096_, v_snd_4118_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4263_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4147_ = v___x_4144_;
v_isShared_4148_ = v_isSharedCheck_4263_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4144_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4263_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v_fst_4149_; lean_object* v_snd_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4262_; 
v_fst_4149_ = lean_ctor_get(v_a_4145_, 0);
v_snd_4150_ = lean_ctor_get(v_a_4145_, 1);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_a_4145_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4152_ = v_a_4145_;
v_isShared_4153_ = v_isSharedCheck_4262_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_snd_4150_);
lean_inc(v_fst_4149_);
lean_dec(v_a_4145_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4262_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_LeanExport_dumpExpr(v_type_4114_, v___y_4096_, v_snd_4150_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v_fst_4156_; lean_object* v_snd_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4253_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
v_fst_4156_ = lean_ctor_get(v_a_4155_, 0);
v_snd_4157_ = lean_ctor_get(v_a_4155_, 1);
v_isSharedCheck_4253_ = !lean_is_exclusive(v_a_4155_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4159_ = v_a_4155_;
v_isShared_4160_ = v_isSharedCheck_4253_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_snd_4157_);
lean_inc(v_fst_4156_);
lean_dec(v_a_4155_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4253_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4161_; 
v___x_4161_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_4104_, v___y_4096_, v_snd_4157_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4252_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4164_ = v___x_4161_;
v_isShared_4165_ = v_isSharedCheck_4252_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4161_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4252_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v_fst_4166_; lean_object* v_snd_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4251_; 
v_fst_4166_ = lean_ctor_get(v_a_4162_, 0);
v_snd_4167_ = lean_ctor_get(v_a_4162_, 1);
v_isSharedCheck_4251_ = !lean_is_exclusive(v_a_4162_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4169_ = v_a_4162_;
v_isShared_4170_ = v_isSharedCheck_4251_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_snd_4167_);
lean_inc(v_fst_4166_);
lean_dec(v_a_4162_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4251_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = lean_box(0);
v___x_4172_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_rules_4109_, v___x_4171_, v___y_4096_, v_snd_4167_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v_fst_4174_; lean_object* v_snd_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4242_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4172_, 1);
v_fst_4174_ = lean_ctor_get(v_a_4173_, 0);
v_snd_4175_ = lean_ctor_get(v_a_4173_, 1);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_a_4173_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4177_ = v_a_4173_;
v_isShared_4178_ = v_isSharedCheck_4242_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_snd_4175_);
lean_inc(v_fst_4174_);
lean_dec(v_a_4173_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4242_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4182_; 
v___x_4179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_4180_ = l_Lean_JsonNumber_fromNat(v_fst_4117_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set_tag(v___x_4164_, 2);
lean_ctor_set(v___x_4164_, 0, v___x_4180_);
v___x_4182_ = v___x_4164_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4180_);
v___x_4182_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
lean_object* v___x_4184_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 1, v___x_4182_);
lean_ctor_set(v___x_4177_, 0, v___x_4179_);
v___x_4184_ = v___x_4177_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v___x_4182_);
v___x_4184_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
lean_object* v___x_4185_; lean_object* v___x_4187_; 
v___x_4185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 1, v_fst_4149_);
lean_ctor_set(v___x_4169_, 0, v___x_4185_);
v___x_4187_ = v___x_4169_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4185_);
lean_ctor_set(v_reuseFailAlloc_4239_, 1, v_fst_4149_);
v___x_4187_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4191_; 
v___x_4188_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4189_ = l_Lean_JsonNumber_fromNat(v_fst_4156_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set_tag(v___x_4147_, 2);
lean_ctor_set(v___x_4147_, 0, v___x_4189_);
v___x_4191_ = v___x_4147_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4189_);
v___x_4191_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4193_; 
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 1, v___x_4191_);
lean_ctor_set(v___x_4159_, 0, v___x_4188_);
v___x_4193_ = v___x_4159_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4194_; lean_object* v___x_4196_; 
v___x_4194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 1, v_fst_4166_);
lean_ctor_set(v___x_4152_, 0, v___x_4194_);
v___x_4196_ = v___x_4152_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v_fst_4166_);
v___x_4196_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4201_; 
v___x_4197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4));
v___x_4198_ = l_Lean_JsonNumber_fromNat(v_numParams_4105_);
v___x_4199_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 1, v___x_4199_);
lean_ctor_set(v___x_4120_, 0, v___x_4197_);
v___x_4201_ = v___x_4120_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4197_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v___x_4199_);
v___x_4201_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0));
v___x_4203_ = l_Lean_JsonNumber_fromNat(v_numIndices_4106_);
v___x_4204_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
v___x_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4202_);
lean_ctor_set(v___x_4205_, 1, v___x_4204_);
v___x_4206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__0));
v___x_4207_ = l_Lean_JsonNumber_fromNat(v_numMotives_4107_);
v___x_4208_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
v___x_4209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4206_);
lean_ctor_set(v___x_4209_, 1, v___x_4208_);
v___x_4210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__1));
v___x_4211_ = l_Lean_JsonNumber_fromNat(v_numMinors_4108_);
v___x_4212_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4211_);
v___x_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4210_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__2));
v___x_4215_ = l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(v_fst_4174_);
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4214_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__3));
v___x_4218_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4218_, 0, v_k_4110_);
v___x_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4217_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
v___x_4220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6));
v___x_4221_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4221_, 0, v_isUnsafe_4111_);
v___x_4222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4220_);
lean_ctor_set(v___x_4222_, 1, v___x_4221_);
v___x_4223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4222_);
lean_ctor_set(v___x_4223_, 1, v___x_4171_);
v___x_4224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4219_);
lean_ctor_set(v___x_4224_, 1, v___x_4223_);
v___x_4225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4216_);
lean_ctor_set(v___x_4225_, 1, v___x_4224_);
v___x_4226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4213_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4209_);
lean_ctor_set(v___x_4227_, 1, v___x_4226_);
v___x_4228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4205_);
lean_ctor_set(v___x_4228_, 1, v___x_4227_);
v___x_4229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4201_);
lean_ctor_set(v___x_4229_, 1, v___x_4228_);
v___x_4230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4196_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4193_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
v___x_4232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4187_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4184_);
lean_ctor_set(v___x_4233_, 1, v___x_4232_);
v___x_4234_ = l_Lean_Json_mkObj(v___x_4233_);
lean_dec_ref_known(v___x_4233_, 2);
v_fst_4125_ = v___x_4234_;
v_snd_4126_ = v_snd_4175_;
goto v___jp_4124_;
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
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_del_object(v___x_4169_);
lean_dec(v_fst_4166_);
lean_del_object(v___x_4164_);
lean_del_object(v___x_4159_);
lean_dec(v_fst_4156_);
lean_del_object(v___x_4152_);
lean_dec(v_fst_4149_);
lean_del_object(v___x_4147_);
lean_dec_ref(v_bs_x27_4123_);
lean_del_object(v___x_4120_);
lean_dec(v_fst_4117_);
lean_dec(v_numMinors_4108_);
lean_dec(v_numMotives_4107_);
lean_dec(v_numIndices_4106_);
lean_dec(v_numParams_4105_);
v_a_4243_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4172_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4172_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4159_);
lean_dec(v_fst_4156_);
lean_del_object(v___x_4152_);
lean_dec(v_fst_4149_);
lean_del_object(v___x_4147_);
lean_del_object(v___x_4120_);
lean_dec(v_fst_4117_);
lean_dec(v_rules_4109_);
lean_dec(v_numMinors_4108_);
lean_dec(v_numMotives_4107_);
lean_dec(v_numIndices_4106_);
lean_dec(v_numParams_4105_);
v___y_4132_ = v___x_4161_;
goto v___jp_4131_;
}
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_del_object(v___x_4152_);
lean_dec(v_fst_4149_);
lean_del_object(v___x_4147_);
lean_dec_ref(v_bs_x27_4123_);
lean_del_object(v___x_4120_);
lean_dec(v_fst_4117_);
lean_dec(v_rules_4109_);
lean_dec(v_numMinors_4108_);
lean_dec(v_numMotives_4107_);
lean_dec(v_numIndices_4106_);
lean_dec(v_numParams_4105_);
lean_dec(v_all_4104_);
v_a_4254_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4154_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4154_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4120_);
lean_dec(v_fst_4117_);
lean_dec_ref(v_type_4114_);
lean_dec(v_rules_4109_);
lean_dec(v_numMinors_4108_);
lean_dec(v_numMotives_4107_);
lean_dec(v_numIndices_4106_);
lean_dec(v_numParams_4105_);
lean_dec(v_all_4104_);
v___y_4132_ = v___x_4144_;
goto v___jp_4131_;
}
v___jp_4124_:
{
size_t v___x_4127_; size_t v___x_4128_; lean_object* v___x_4129_; 
v___x_4127_ = ((size_t)1ULL);
v___x_4128_ = lean_usize_add(v_i_4094_, v___x_4127_);
v___x_4129_ = lean_array_uset(v_bs_x27_4123_, v_i_4094_, v_fst_4125_);
v_i_4094_ = v___x_4128_;
v_bs_4095_ = v___x_4129_;
v___y_4097_ = v_snd_4126_;
goto _start;
}
v___jp_4131_:
{
if (lean_obj_tag(v___y_4132_) == 0)
{
lean_object* v_a_4133_; lean_object* v_fst_4134_; lean_object* v_snd_4135_; 
v_a_4133_ = lean_ctor_get(v___y_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___y_4132_, 1);
v_fst_4134_ = lean_ctor_get(v_a_4133_, 0);
lean_inc(v_fst_4134_);
v_snd_4135_ = lean_ctor_get(v_a_4133_, 1);
lean_inc(v_snd_4135_);
lean_dec(v_a_4133_);
v_fst_4125_ = v_fst_4134_;
v_snd_4126_ = v_snd_4135_;
goto v___jp_4124_;
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec_ref(v_bs_x27_4123_);
v_a_4136_ = lean_ctor_get(v___y_4132_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___y_4132_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___y_4132_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___y_4132_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec_ref(v_type_4114_);
lean_dec(v_levelParams_4113_);
lean_dec(v_rules_4109_);
lean_dec(v_numMinors_4108_);
lean_dec(v_numMotives_4107_);
lean_dec(v_numIndices_4106_);
lean_dec(v_numParams_4105_);
lean_dec(v_all_4104_);
lean_dec_ref(v_bs_4095_);
v_a_4265_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4115_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4115_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(uint8_t v___x_4321_, lean_object* v_as_x27_4322_, lean_object* v_b_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
if (lean_obj_tag(v_as_x27_4322_) == 0)
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4327_, 0, v_b_4323_);
lean_ctor_set(v___x_4327_, 1, v___y_4325_);
v___x_4328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4328_, 0, v___x_4327_);
return v___x_4328_;
}
else
{
lean_object* v_head_4329_; lean_object* v_tail_4330_; lean_object* v___x_4331_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___x_4362_; 
lean_dec_ref(v_b_4323_);
v_head_4329_ = lean_ctor_get(v_as_x27_4322_, 0);
v_tail_4330_ = lean_ctor_get(v_as_x27_4322_, 1);
v___x_4331_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
lean_inc(v_head_4329_);
lean_inc_ref(v___y_4324_);
v___x_4362_ = l_Lean_Environment_find_x3f(v___y_4324_, v_head_4329_, v___x_4321_);
if (lean_obj_tag(v___x_4362_) == 1)
{
lean_object* v_val_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4486_; 
v_val_4363_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4365_ = v___x_4362_;
v_isShared_4366_ = v_isSharedCheck_4486_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_val_4363_);
lean_dec(v___x_4362_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4486_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
if (lean_obj_tag(v_val_4363_) == 4)
{
lean_object* v_val_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4485_; 
v_val_4367_ = lean_ctor_get(v_val_4363_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_val_4363_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4369_ = v_val_4363_;
v_isShared_4370_ = v_isSharedCheck_4485_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_val_4367_);
lean_dec(v_val_4363_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4485_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v_toConstantVal_4371_; lean_object* v_visitedNames_4372_; lean_object* v_visitedLevels_4373_; lean_object* v_visitedExprs_4374_; lean_object* v_visitedConstants_4375_; lean_object* v_noMDataExprs_4376_; uint8_t v_exportMData_4377_; uint8_t v_exportUnsafe_4378_; uint8_t v_ignoreMissing_4379_; lean_object* v_recursorMap_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4484_; 
v_toConstantVal_4371_ = lean_ctor_get(v_val_4367_, 0);
lean_inc_ref(v_toConstantVal_4371_);
v_visitedNames_4372_ = lean_ctor_get(v___y_4325_, 0);
v_visitedLevels_4373_ = lean_ctor_get(v___y_4325_, 1);
v_visitedExprs_4374_ = lean_ctor_get(v___y_4325_, 2);
v_visitedConstants_4375_ = lean_ctor_get(v___y_4325_, 3);
v_noMDataExprs_4376_ = lean_ctor_get(v___y_4325_, 4);
v_exportMData_4377_ = lean_ctor_get_uint8(v___y_4325_, sizeof(void*)*6);
v_exportUnsafe_4378_ = lean_ctor_get_uint8(v___y_4325_, sizeof(void*)*6 + 1);
v_ignoreMissing_4379_ = lean_ctor_get_uint8(v___y_4325_, sizeof(void*)*6 + 2);
v_recursorMap_4380_ = lean_ctor_get(v___y_4325_, 5);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___y_4325_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4382_ = v___y_4325_;
v_isShared_4383_ = v_isSharedCheck_4484_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_recursorMap_4380_);
lean_inc(v_noMDataExprs_4376_);
lean_inc(v_visitedConstants_4375_);
lean_inc(v_visitedExprs_4374_);
lean_inc(v_visitedLevels_4373_);
lean_inc(v_visitedNames_4372_);
lean_dec(v___y_4325_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4484_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
uint8_t v_kind_4384_; lean_object* v_name_4385_; lean_object* v_levelParams_4386_; lean_object* v_type_4387_; lean_object* v___x_4388_; lean_object* v___x_4390_; 
v_kind_4384_ = lean_ctor_get_uint8(v_val_4367_, sizeof(void*)*1);
lean_dec_ref(v_val_4367_);
v_name_4385_ = lean_ctor_get(v_toConstantVal_4371_, 0);
lean_inc(v_name_4385_);
v_levelParams_4386_ = lean_ctor_get(v_toConstantVal_4371_, 1);
lean_inc(v_levelParams_4386_);
v_type_4387_ = lean_ctor_get(v_toConstantVal_4371_, 2);
lean_inc_ref(v_type_4387_);
lean_dec_ref(v_toConstantVal_4371_);
lean_inc(v_head_4329_);
v___x_4388_ = l_Lean_NameHashSet_insert(v_visitedConstants_4375_, v_head_4329_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 3, v___x_4388_);
v___x_4390_ = v___x_4382_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_visitedNames_4372_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v_visitedLevels_4373_);
lean_ctor_set(v_reuseFailAlloc_4483_, 2, v_visitedExprs_4374_);
lean_ctor_set(v_reuseFailAlloc_4483_, 3, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4483_, 4, v_noMDataExprs_4376_);
lean_ctor_set(v_reuseFailAlloc_4483_, 5, v_recursorMap_4380_);
lean_ctor_set_uint8(v_reuseFailAlloc_4483_, sizeof(void*)*6, v_exportMData_4377_);
lean_ctor_set_uint8(v_reuseFailAlloc_4483_, sizeof(void*)*6 + 1, v_exportUnsafe_4378_);
lean_ctor_set_uint8(v_reuseFailAlloc_4483_, sizeof(void*)*6 + 2, v_ignoreMissing_4379_);
v___x_4390_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; 
v___x_4391_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4385_, v___y_4324_, v___x_4390_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v_fst_4393_; lean_object* v_snd_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4474_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v___x_4391_, 1);
v_fst_4393_ = lean_ctor_get(v_a_4392_, 0);
v_snd_4394_ = lean_ctor_get(v_a_4392_, 1);
v_isSharedCheck_4474_ = !lean_is_exclusive(v_a_4392_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4396_ = v_a_4392_;
v_isShared_4397_ = v_isSharedCheck_4474_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_snd_4394_);
lean_inc(v_fst_4393_);
lean_dec(v_a_4392_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4474_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; 
v___x_4398_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4386_, v___y_4324_, v_snd_4394_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v_fst_4400_; lean_object* v_snd_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4465_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v_fst_4400_ = lean_ctor_get(v_a_4399_, 0);
v_snd_4401_ = lean_ctor_get(v_a_4399_, 1);
v_isSharedCheck_4465_ = !lean_is_exclusive(v_a_4399_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4403_ = v_a_4399_;
v_isShared_4404_ = v_isSharedCheck_4465_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_snd_4401_);
lean_inc(v_fst_4400_);
lean_dec(v_a_4399_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4465_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; 
v___x_4405_ = l_LeanExport_dumpExpr(v_type_4387_, v___y_4324_, v_snd_4401_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v_fst_4407_; lean_object* v_snd_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4456_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4405_, 1);
v_fst_4407_ = lean_ctor_get(v_a_4406_, 0);
v_snd_4408_ = lean_ctor_get(v_a_4406_, 1);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_a_4406_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4410_ = v_a_4406_;
v_isShared_4411_ = v_isSharedCheck_4456_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_snd_4408_);
lean_inc(v_fst_4407_);
lean_dec(v_a_4406_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4456_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; 
v___x_4412_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5));
v___x_4413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_4414_ = l_Lean_JsonNumber_fromNat(v_fst_4393_);
if (v_isShared_4370_ == 0)
{
lean_ctor_set_tag(v___x_4369_, 2);
lean_ctor_set(v___x_4369_, 0, v___x_4414_);
v___x_4416_ = v___x_4369_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4418_; 
if (v_isShared_4411_ == 0)
{
lean_ctor_set(v___x_4410_, 1, v___x_4416_);
lean_ctor_set(v___x_4410_, 0, v___x_4413_);
v___x_4418_ = v___x_4410_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4454_, 1, v___x_4416_);
v___x_4418_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4419_; lean_object* v___x_4421_; 
v___x_4419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 1, v_fst_4400_);
lean_ctor_set(v___x_4403_, 0, v___x_4419_);
v___x_4421_ = v___x_4403_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4419_);
lean_ctor_set(v_reuseFailAlloc_4453_, 1, v_fst_4400_);
v___x_4421_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4425_; 
v___x_4422_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4423_ = l_Lean_JsonNumber_fromNat(v_fst_4407_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set_tag(v___x_4365_, 2);
lean_ctor_set(v___x_4365_, 0, v___x_4423_);
v___x_4425_ = v___x_4365_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4423_);
v___x_4425_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
lean_object* v___x_4427_; 
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 1, v___x_4425_);
lean_ctor_set(v___x_4396_, 0, v___x_4422_);
v___x_4427_ = v___x_4396_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4451_, 1, v___x_4425_);
v___x_4427_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4428_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6));
v___x_4429_ = l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(v_kind_4384_);
v___x_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4428_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
v___x_4431_ = lean_box(0);
v___x_4432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4430_);
lean_ctor_set(v___x_4432_, 1, v___x_4431_);
v___x_4433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4427_);
lean_ctor_set(v___x_4433_, 1, v___x_4432_);
v___x_4434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4421_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
v___x_4435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4418_);
lean_ctor_set(v___x_4435_, 1, v___x_4434_);
v___x_4436_ = l_Lean_Json_mkObj(v___x_4435_);
lean_dec_ref_known(v___x_4435_, 2);
v___x_4437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4412_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v___x_4438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
lean_ctor_set(v___x_4438_, 1, v___x_4431_);
v___x_4439_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4438_, v_snd_4408_);
lean_dec_ref_known(v___x_4438_, 2);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v_a_4440_; lean_object* v_snd_4441_; 
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_a_4440_);
lean_dec_ref_known(v___x_4439_, 1);
v_snd_4441_ = lean_ctor_get(v_a_4440_, 1);
lean_inc(v_snd_4441_);
lean_dec(v_a_4440_);
v_as_x27_4322_ = v_tail_4330_;
v_b_4323_ = v___x_4331_;
v___y_4325_ = v_snd_4441_;
goto _start;
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
v_a_4443_ = lean_ctor_get(v___x_4439_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4439_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4439_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
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
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_del_object(v___x_4403_);
lean_dec(v_fst_4400_);
lean_del_object(v___x_4396_);
lean_dec(v_fst_4393_);
lean_del_object(v___x_4369_);
lean_del_object(v___x_4365_);
v_a_4457_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4405_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4405_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
lean_del_object(v___x_4396_);
lean_dec(v_fst_4393_);
lean_dec_ref(v_type_4387_);
lean_del_object(v___x_4369_);
lean_del_object(v___x_4365_);
v_a_4466_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4468_ = v___x_4398_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4398_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec_ref(v_type_4387_);
lean_dec(v_levelParams_4386_);
lean_del_object(v___x_4369_);
lean_del_object(v___x_4365_);
v_a_4475_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4391_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4391_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_4365_);
lean_dec(v_val_4363_);
v___y_4333_ = v___y_4324_;
v___y_4334_ = v___y_4325_;
goto v___jp_4332_;
}
}
}
else
{
lean_dec(v___x_4362_);
v___y_4333_ = v___y_4324_;
v___y_4334_ = v___y_4325_;
goto v___jp_4332_;
}
v___jp_4332_:
{
uint8_t v_ignoreMissing_4335_; 
v_ignoreMissing_4335_ = lean_ctor_get_uint8(v___y_4334_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_4335_ == 0)
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4336_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4337_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_4338_ = lean_unsigned_to_nat(313u);
v___x_4339_ = lean_unsigned_to_nat(52u);
v___x_4340_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_4341_ = 1;
lean_inc(v_head_4329_);
v___x_4342_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_4329_, v___x_4341_);
v___x_4343_ = lean_string_append(v___x_4340_, v___x_4342_);
lean_dec_ref(v___x_4342_);
v___x_4344_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_4345_ = lean_string_append(v___x_4343_, v___x_4344_);
v___x_4346_ = l_mkPanicMessageWithDecl(v___x_4336_, v___x_4337_, v___x_4338_, v___x_4339_, v___x_4345_);
lean_dec_ref(v___x_4345_);
v___x_4347_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_4346_, v___y_4333_, v___y_4334_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; lean_object* v_snd_4349_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v___x_4347_, 1);
v_snd_4349_ = lean_ctor_get(v_a_4348_, 1);
lean_inc(v_snd_4349_);
lean_dec(v_a_4348_);
v_as_x27_4322_ = v_tail_4330_;
v_b_4323_ = v___x_4331_;
v___y_4325_ = v_snd_4349_;
goto _start;
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
v_a_4351_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4347_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4347_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
else
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4359_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4));
v___x_4360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
lean_ctor_set(v___x_4360_, 1, v___y_4334_);
v___x_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4360_);
return v___x_4361_;
}
}
}
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__21(void){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4489_ = l_Lean_NameSet_empty;
v___x_4490_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4490_);
lean_ctor_set(v___x_4491_, 1, v___x_4489_);
return v___x_4491_;
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__22(void){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4492_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__21, &l_LeanExport_dumpConstant___closed__21_once, _init_l_LeanExport_dumpConstant___closed__21);
v___x_4493_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
lean_ctor_set(v___x_4494_, 1, v___x_4492_);
return v___x_4494_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4497_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1));
v___x_4498_ = lean_unsigned_to_nat(11u);
v___x_4499_ = lean_unsigned_to_nat(341u);
v___x_4500_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_4501_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4502_ = l_mkPanicMessageWithDecl(v___x_4501_, v___x_4500_, v___x_4499_, v___x_4498_, v___x_4497_);
return v___x_4502_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4504_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3));
v___x_4505_ = lean_unsigned_to_nat(6u);
v___x_4506_ = lean_unsigned_to_nat(329u);
v___x_4507_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_4508_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4509_ = l_mkPanicMessageWithDecl(v___x_4508_, v___x_4507_, v___x_4506_, v___x_4505_, v___x_4504_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(uint8_t v___x_4510_, lean_object* v_val_4511_, lean_object* v_as_x27_4512_, lean_object* v_b_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
if (lean_obj_tag(v_as_x27_4512_) == 0)
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4517_, 0, v_b_4513_);
lean_ctor_set(v___x_4517_, 1, v___y_4515_);
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
else
{
lean_object* v_head_4519_; lean_object* v_tail_4520_; lean_object* v___y_4522_; lean_object* v_snd_4553_; lean_object* v_fst_4554_; lean_object* v_fst_4555_; lean_object* v_snd_4556_; lean_object* v___y_4558_; uint8_t v___y_4559_; lean_object* v___y_4640_; lean_object* v___x_4647_; 
v_head_4519_ = lean_ctor_get(v_as_x27_4512_, 0);
v_tail_4520_ = lean_ctor_get(v_as_x27_4512_, 1);
v_snd_4553_ = lean_ctor_get(v_b_4513_, 1);
lean_inc(v_snd_4553_);
v_fst_4554_ = lean_ctor_get(v_b_4513_, 0);
lean_inc(v_fst_4554_);
lean_dec_ref(v_b_4513_);
v_fst_4555_ = lean_ctor_get(v_snd_4553_, 0);
lean_inc(v_fst_4555_);
v_snd_4556_ = lean_ctor_get(v_snd_4553_, 1);
lean_inc(v_snd_4556_);
lean_dec(v_snd_4553_);
lean_inc(v_head_4519_);
lean_inc_ref(v___y_4514_);
v___x_4647_ = l_Lean_Environment_find_x3f(v___y_4514_, v_head_4519_, v___x_4510_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4648_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8);
v___x_4649_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_4648_);
v___y_4640_ = v___x_4649_;
goto v___jp_4639_;
}
else
{
lean_object* v_val_4650_; 
v_val_4650_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_val_4650_);
lean_dec_ref_known(v___x_4647_, 1);
v___y_4640_ = v_val_4650_;
goto v___jp_4639_;
}
v___jp_4521_:
{
if (lean_obj_tag(v___y_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4544_; 
v_a_4523_ = lean_ctor_get(v___y_4522_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___y_4522_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4525_ = v___y_4522_;
v_isShared_4526_ = v_isSharedCheck_4544_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___y_4522_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4544_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v_fst_4527_; 
v_fst_4527_ = lean_ctor_get(v_a_4523_, 0);
lean_inc(v_fst_4527_);
if (lean_obj_tag(v_fst_4527_) == 0)
{
lean_object* v_snd_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4539_; 
v_snd_4528_ = lean_ctor_get(v_a_4523_, 1);
v_isSharedCheck_4539_ = !lean_is_exclusive(v_a_4523_);
if (v_isSharedCheck_4539_ == 0)
{
lean_object* v_unused_4540_; 
v_unused_4540_ = lean_ctor_get(v_a_4523_, 0);
lean_dec(v_unused_4540_);
v___x_4530_ = v_a_4523_;
v_isShared_4531_ = v_isSharedCheck_4539_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_snd_4528_);
lean_dec(v_a_4523_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4539_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v_a_4532_; lean_object* v___x_4534_; 
v_a_4532_ = lean_ctor_get(v_fst_4527_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v_fst_4527_, 1);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v_a_4532_);
v___x_4534_ = v___x_4530_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4532_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v_snd_4528_);
v___x_4534_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
lean_object* v___x_4536_; 
if (v_isShared_4526_ == 0)
{
lean_ctor_set(v___x_4525_, 0, v___x_4534_);
v___x_4536_ = v___x_4525_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
else
{
lean_object* v_snd_4541_; lean_object* v_a_4542_; 
lean_del_object(v___x_4525_);
v_snd_4541_ = lean_ctor_get(v_a_4523_, 1);
lean_inc(v_snd_4541_);
lean_dec(v_a_4523_);
v_a_4542_ = lean_ctor_get(v_fst_4527_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v_fst_4527_, 1);
v_as_x27_4512_ = v_tail_4520_;
v_b_4513_ = v_a_4542_;
v___y_4515_ = v_snd_4541_;
goto _start;
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
v_a_4545_ = lean_ctor_get(v___y_4522_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___y_4522_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___y_4522_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___y_4522_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
v___jp_4557_:
{
lean_object* v_toConstantVal_4560_; lean_object* v_ctors_4561_; lean_object* v___x_4562_; 
v_toConstantVal_4560_ = lean_ctor_get(v___y_4558_, 0);
v_ctors_4561_ = lean_ctor_get(v___y_4558_, 4);
v___x_4562_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_4559_, v___x_4510_, v_ctors_4561_, v_fst_4555_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; lean_object* v_snd_4564_; lean_object* v_fst_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4630_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_a_4563_);
lean_dec_ref_known(v___x_4562_, 1);
v_snd_4564_ = lean_ctor_get(v_a_4563_, 1);
v_fst_4565_ = lean_ctor_get(v_a_4563_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v_a_4563_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4567_ = v_a_4563_;
v_isShared_4568_ = v_isSharedCheck_4630_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_snd_4564_);
lean_inc(v_fst_4565_);
lean_dec(v_a_4563_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4630_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v_visitedNames_4569_; lean_object* v_visitedLevels_4570_; lean_object* v_visitedExprs_4571_; lean_object* v_visitedConstants_4572_; lean_object* v_noMDataExprs_4573_; uint8_t v_exportMData_4574_; uint8_t v_exportUnsafe_4575_; uint8_t v_ignoreMissing_4576_; lean_object* v_recursorMap_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4629_; 
v_visitedNames_4569_ = lean_ctor_get(v_snd_4564_, 0);
v_visitedLevels_4570_ = lean_ctor_get(v_snd_4564_, 1);
v_visitedExprs_4571_ = lean_ctor_get(v_snd_4564_, 2);
v_visitedConstants_4572_ = lean_ctor_get(v_snd_4564_, 3);
v_noMDataExprs_4573_ = lean_ctor_get(v_snd_4564_, 4);
v_exportMData_4574_ = lean_ctor_get_uint8(v_snd_4564_, sizeof(void*)*6);
v_exportUnsafe_4575_ = lean_ctor_get_uint8(v_snd_4564_, sizeof(void*)*6 + 1);
v_ignoreMissing_4576_ = lean_ctor_get_uint8(v_snd_4564_, sizeof(void*)*6 + 2);
v_recursorMap_4577_ = lean_ctor_get(v_snd_4564_, 5);
v_isSharedCheck_4629_ = !lean_is_exclusive(v_snd_4564_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4579_ = v_snd_4564_;
v_isShared_4580_ = v_isSharedCheck_4629_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_recursorMap_4577_);
lean_inc(v_noMDataExprs_4573_);
lean_inc(v_visitedConstants_4572_);
lean_inc(v_visitedExprs_4571_);
lean_inc(v_visitedLevels_4570_);
lean_inc(v_visitedNames_4569_);
lean_dec(v_snd_4564_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4629_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v_type_4581_; lean_object* v___x_4582_; lean_object* v___x_4584_; 
v_type_4581_ = lean_ctor_get(v_toConstantVal_4560_, 2);
lean_inc(v_head_4519_);
v___x_4582_ = l_Lean_NameHashSet_insert(v_visitedConstants_4572_, v_head_4519_);
if (v_isShared_4580_ == 0)
{
lean_ctor_set(v___x_4579_, 3, v___x_4582_);
v___x_4584_ = v___x_4579_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_visitedNames_4569_);
lean_ctor_set(v_reuseFailAlloc_4628_, 1, v_visitedLevels_4570_);
lean_ctor_set(v_reuseFailAlloc_4628_, 2, v_visitedExprs_4571_);
lean_ctor_set(v_reuseFailAlloc_4628_, 3, v___x_4582_);
lean_ctor_set(v_reuseFailAlloc_4628_, 4, v_noMDataExprs_4573_);
lean_ctor_set(v_reuseFailAlloc_4628_, 5, v_recursorMap_4577_);
lean_ctor_set_uint8(v_reuseFailAlloc_4628_, sizeof(void*)*6, v_exportMData_4574_);
lean_ctor_set_uint8(v_reuseFailAlloc_4628_, sizeof(void*)*6 + 1, v_exportUnsafe_4575_);
lean_ctor_set_uint8(v_reuseFailAlloc_4628_, sizeof(void*)*6 + 2, v_ignoreMissing_4576_);
v___x_4584_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; 
lean_inc_ref(v_type_4581_);
v___x_4585_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4581_, v___y_4514_, v___x_4584_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v_a_4586_; lean_object* v_snd_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4618_; 
v_a_4586_ = lean_ctor_get(v___x_4585_, 0);
lean_inc(v_a_4586_);
lean_dec_ref_known(v___x_4585_, 1);
v_snd_4587_ = lean_ctor_get(v_a_4586_, 1);
v_isSharedCheck_4618_ = !lean_is_exclusive(v_a_4586_);
if (v_isSharedCheck_4618_ == 0)
{
lean_object* v_unused_4619_; 
v_unused_4619_ = lean_ctor_get(v_a_4586_, 0);
lean_dec(v_unused_4619_);
v___x_4589_ = v_a_4586_;
v_isShared_4590_ = v_isSharedCheck_4618_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_snd_4587_);
lean_dec(v_a_4586_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4618_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v_toConstantVal_4591_; lean_object* v_recursorMap_4592_; lean_object* v_name_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v_toConstantVal_4591_ = lean_ctor_get(v_val_4511_, 0);
v_recursorMap_4592_ = lean_ctor_get(v_snd_4587_, 5);
v_name_4593_ = lean_ctor_get(v_toConstantVal_4591_, 0);
v___x_4594_ = lean_array_push(v_fst_4554_, v___y_4558_);
v___x_4595_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_recursorMap_4592_, v_name_4593_);
if (lean_obj_tag(v___x_4595_) == 1)
{
lean_object* v_val_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4600_; 
v_val_4596_ = lean_ctor_get(v___x_4595_, 0);
lean_inc(v_val_4596_);
lean_dec_ref_known(v___x_4595_, 1);
v___x_4597_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0));
v___x_4598_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v___x_4597_, v_snd_4556_, v_val_4596_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 1, v___x_4598_);
lean_ctor_set(v___x_4589_, 0, v_fst_4565_);
v___x_4600_ = v___x_4589_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_fst_4565_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v___x_4598_);
v___x_4600_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
lean_object* v___x_4602_; 
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 1, v___x_4600_);
lean_ctor_set(v___x_4567_, 0, v___x_4594_);
v___x_4602_ = v___x_4567_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v___x_4594_);
lean_ctor_set(v_reuseFailAlloc_4604_, 1, v___x_4600_);
v___x_4602_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
v_as_x27_4512_ = v_tail_4520_;
v_b_4513_ = v___x_4602_;
v___y_4515_ = v_snd_4587_;
goto _start;
}
}
}
else
{
lean_object* v___x_4606_; lean_object* v___x_4607_; uint8_t v___x_4608_; 
lean_dec(v___x_4595_);
v___x_4606_ = lean_array_get_size(v_fst_4565_);
v___x_4607_ = lean_unsigned_to_nat(0u);
v___x_4608_ = lean_nat_dec_eq(v___x_4606_, v___x_4607_);
if (v___x_4608_ == 0)
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
lean_dec_ref(v___x_4594_);
lean_del_object(v___x_4589_);
lean_del_object(v___x_4567_);
lean_dec(v_fst_4565_);
lean_dec(v_snd_4556_);
v___x_4609_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2);
v___x_4610_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4609_, v___y_4514_, v_snd_4587_);
v___y_4522_ = v___x_4610_;
goto v___jp_4521_;
}
else
{
lean_object* v___x_4612_; 
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 1, v_snd_4556_);
lean_ctor_set(v___x_4589_, 0, v_fst_4565_);
v___x_4612_ = v___x_4589_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_fst_4565_);
lean_ctor_set(v_reuseFailAlloc_4617_, 1, v_snd_4556_);
v___x_4612_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
lean_object* v___x_4614_; 
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 1, v___x_4612_);
lean_ctor_set(v___x_4567_, 0, v___x_4594_);
v___x_4614_ = v___x_4567_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4594_);
lean_ctor_set(v_reuseFailAlloc_4616_, 1, v___x_4612_);
v___x_4614_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
v_as_x27_4512_ = v_tail_4520_;
v_b_4513_ = v___x_4614_;
v___y_4515_ = v_snd_4587_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
lean_del_object(v___x_4567_);
lean_dec(v_fst_4565_);
lean_dec_ref(v___y_4558_);
lean_dec(v_snd_4556_);
lean_dec(v_fst_4554_);
v_a_4620_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4622_ = v___x_4585_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4585_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4620_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_dec_ref(v___y_4558_);
lean_dec(v_snd_4556_);
lean_dec(v_fst_4554_);
v_a_4631_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4562_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4562_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
v___jp_4639_:
{
lean_object* v___x_4641_; uint8_t v_isUnsafe_4642_; 
v___x_4641_ = l_Lean_ConstantInfo_inductiveVal_x21(v___y_4640_);
lean_dec_ref(v___y_4640_);
v_isUnsafe_4642_ = lean_ctor_get_uint8(v___x_4641_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4642_ == 0)
{
uint8_t v___x_4643_; 
v___x_4643_ = 1;
v___y_4558_ = v___x_4641_;
v___y_4559_ = v___x_4643_;
goto v___jp_4557_;
}
else
{
if (v___x_4510_ == 0)
{
uint8_t v_exportUnsafe_4644_; 
v_exportUnsafe_4644_ = lean_ctor_get_uint8(v___y_4515_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_4644_ == 0)
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
lean_dec_ref(v___x_4641_);
lean_dec(v_snd_4556_);
lean_dec(v_fst_4555_);
lean_dec(v_fst_4554_);
v___x_4645_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4);
v___x_4646_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4645_, v___y_4514_, v___y_4515_);
v___y_4522_ = v___x_4646_;
goto v___jp_4521_;
}
else
{
v___y_4558_ = v___x_4641_;
v___y_4559_ = v_exportUnsafe_4644_;
goto v___jp_4557_;
}
}
else
{
v___y_4558_ = v___x_4641_;
v___y_4559_ = v___x_4510_;
goto v___jp_4557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object* v_as_4651_, size_t v_sz_4652_, size_t v_i_4653_, lean_object* v_b_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
uint8_t v___x_4658_; 
v___x_4658_ = lean_usize_dec_lt(v_i_4653_, v_sz_4652_);
if (v___x_4658_ == 0)
{
lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4659_, 0, v_b_4654_);
lean_ctor_set(v___x_4659_, 1, v___y_4656_);
v___x_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4659_);
return v___x_4660_;
}
else
{
lean_object* v_visitedNames_4661_; lean_object* v_visitedLevels_4662_; lean_object* v_visitedExprs_4663_; lean_object* v_visitedConstants_4664_; lean_object* v_noMDataExprs_4665_; uint8_t v_exportMData_4666_; uint8_t v_exportUnsafe_4667_; uint8_t v_ignoreMissing_4668_; lean_object* v_recursorMap_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4688_; 
v_visitedNames_4661_ = lean_ctor_get(v___y_4656_, 0);
v_visitedLevels_4662_ = lean_ctor_get(v___y_4656_, 1);
v_visitedExprs_4663_ = lean_ctor_get(v___y_4656_, 2);
v_visitedConstants_4664_ = lean_ctor_get(v___y_4656_, 3);
v_noMDataExprs_4665_ = lean_ctor_get(v___y_4656_, 4);
v_exportMData_4666_ = lean_ctor_get_uint8(v___y_4656_, sizeof(void*)*6);
v_exportUnsafe_4667_ = lean_ctor_get_uint8(v___y_4656_, sizeof(void*)*6 + 1);
v_ignoreMissing_4668_ = lean_ctor_get_uint8(v___y_4656_, sizeof(void*)*6 + 2);
v_recursorMap_4669_ = lean_ctor_get(v___y_4656_, 5);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___y_4656_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4671_ = v___y_4656_;
v_isShared_4672_ = v_isSharedCheck_4688_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_recursorMap_4669_);
lean_inc(v_noMDataExprs_4665_);
lean_inc(v_visitedConstants_4664_);
lean_inc(v_visitedExprs_4663_);
lean_inc(v_visitedLevels_4662_);
lean_inc(v_visitedNames_4661_);
lean_dec(v___y_4656_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4688_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v_a_4673_; lean_object* v_toConstantVal_4674_; lean_object* v_name_4675_; lean_object* v_type_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
v_a_4673_ = lean_array_uget_borrowed(v_as_4651_, v_i_4653_);
v_toConstantVal_4674_ = lean_ctor_get(v_a_4673_, 0);
v_name_4675_ = lean_ctor_get(v_toConstantVal_4674_, 0);
v_type_4676_ = lean_ctor_get(v_toConstantVal_4674_, 2);
lean_inc(v_name_4675_);
v___x_4677_ = l_Lean_NameHashSet_insert(v_visitedConstants_4664_, v_name_4675_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 3, v___x_4677_);
v___x_4679_ = v___x_4671_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_visitedNames_4661_);
lean_ctor_set(v_reuseFailAlloc_4687_, 1, v_visitedLevels_4662_);
lean_ctor_set(v_reuseFailAlloc_4687_, 2, v_visitedExprs_4663_);
lean_ctor_set(v_reuseFailAlloc_4687_, 3, v___x_4677_);
lean_ctor_set(v_reuseFailAlloc_4687_, 4, v_noMDataExprs_4665_);
lean_ctor_set(v_reuseFailAlloc_4687_, 5, v_recursorMap_4669_);
lean_ctor_set_uint8(v_reuseFailAlloc_4687_, sizeof(void*)*6, v_exportMData_4666_);
lean_ctor_set_uint8(v_reuseFailAlloc_4687_, sizeof(void*)*6 + 1, v_exportUnsafe_4667_);
lean_ctor_set_uint8(v_reuseFailAlloc_4687_, sizeof(void*)*6 + 2, v_ignoreMissing_4668_);
v___x_4679_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
lean_object* v___x_4680_; 
lean_inc_ref(v_type_4676_);
v___x_4680_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4676_, v___y_4655_, v___x_4679_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v_snd_4682_; lean_object* v___x_4683_; size_t v___x_4684_; size_t v___x_4685_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4681_);
lean_dec_ref_known(v___x_4680_, 1);
v_snd_4682_ = lean_ctor_get(v_a_4681_, 1);
lean_inc(v_snd_4682_);
lean_dec(v_a_4681_);
v___x_4683_ = lean_box(0);
v___x_4684_ = ((size_t)1ULL);
v___x_4685_ = lean_usize_add(v_i_4653_, v___x_4684_);
v_i_4653_ = v___x_4685_;
v_b_4654_ = v___x_4683_;
v___y_4656_ = v_snd_4682_;
goto _start;
}
else
{
return v___x_4680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(lean_object* v_as_x27_4689_, lean_object* v_b_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
if (lean_obj_tag(v_as_x27_4689_) == 0)
{
lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4694_, 0, v_b_4690_);
lean_ctor_set(v___x_4694_, 1, v___y_4692_);
v___x_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4694_);
return v___x_4695_;
}
else
{
lean_object* v_head_4696_; lean_object* v_tail_4697_; lean_object* v___x_4698_; 
v_head_4696_ = lean_ctor_get(v_as_x27_4689_, 0);
v_tail_4697_ = lean_ctor_get(v_as_x27_4689_, 1);
lean_inc(v_head_4696_);
v___x_4698_ = l_LeanExport_dumpConstant(v_head_4696_, v___y_4691_, v___y_4692_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v_snd_4700_; lean_object* v___x_4701_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
lean_inc(v_a_4699_);
lean_dec_ref_known(v___x_4698_, 1);
v_snd_4700_ = lean_ctor_get(v_a_4699_, 1);
lean_inc(v_snd_4700_);
lean_dec(v_a_4699_);
v___x_4701_ = lean_box(0);
v_as_x27_4689_ = v_tail_4697_;
v_b_4690_ = v___x_4701_;
v___y_4692_ = v_snd_4700_;
goto _start;
}
else
{
return v___x_4698_;
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant(lean_object* v_c_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v___y_4712_; lean_object* v___y_4713_; size_t v___y_4714_; lean_object* v___y_4715_; size_t v___y_4716_; lean_object* v_fst_4717_; lean_object* v_snd_4718_; uint8_t v___x_4813_; lean_object* v___x_4814_; 
v___x_4813_ = 0;
lean_inc(v_c_4703_);
lean_inc_ref(v_a_4704_);
v___x_4814_ = l_Lean_Environment_find_x3f(v_a_4704_, v_c_4703_, v___x_4813_);
if (lean_obj_tag(v___x_4814_) == 1)
{
lean_object* v_val_4815_; uint8_t v___y_5554_; uint8_t v___x_5555_; 
v_val_4815_ = lean_ctor_get(v___x_4814_, 0);
lean_inc(v_val_4815_);
lean_dec_ref_known(v___x_4814_, 1);
v___x_5555_ = l_Lean_ConstantInfo_isUnsafe(v_val_4815_);
if (v___x_5555_ == 0)
{
v___y_5554_ = v___x_5555_;
goto v___jp_5553_;
}
else
{
uint8_t v_exportUnsafe_5556_; 
v_exportUnsafe_5556_ = lean_ctor_get_uint8(v_a_4705_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_5556_ == 0)
{
v___y_5554_ = v___x_5555_;
goto v___jp_5553_;
}
else
{
goto v___jp_4816_;
}
}
v___jp_4816_:
{
lean_object* v_visitedNames_4817_; lean_object* v_visitedLevels_4818_; lean_object* v_visitedExprs_4819_; lean_object* v_visitedConstants_4820_; lean_object* v_noMDataExprs_4821_; uint8_t v_exportMData_4822_; uint8_t v_exportUnsafe_4823_; uint8_t v_ignoreMissing_4824_; lean_object* v_recursorMap_4825_; uint8_t v___x_4826_; 
v_visitedNames_4817_ = lean_ctor_get(v_a_4705_, 0);
v_visitedLevels_4818_ = lean_ctor_get(v_a_4705_, 1);
v_visitedExprs_4819_ = lean_ctor_get(v_a_4705_, 2);
v_visitedConstants_4820_ = lean_ctor_get(v_a_4705_, 3);
v_noMDataExprs_4821_ = lean_ctor_get(v_a_4705_, 4);
v_exportMData_4822_ = lean_ctor_get_uint8(v_a_4705_, sizeof(void*)*6);
v_exportUnsafe_4823_ = lean_ctor_get_uint8(v_a_4705_, sizeof(void*)*6 + 1);
v_ignoreMissing_4824_ = lean_ctor_get_uint8(v_a_4705_, sizeof(void*)*6 + 2);
v_recursorMap_4825_ = lean_ctor_get(v_a_4705_, 5);
v___x_4826_ = l_Lean_NameHashSet_contains(v_visitedConstants_4820_, v_c_4703_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_5546_; 
lean_inc(v_recursorMap_4825_);
lean_inc_ref(v_noMDataExprs_4821_);
lean_inc_ref(v_visitedConstants_4820_);
lean_inc_ref(v_visitedExprs_4819_);
lean_inc_ref(v_visitedLevels_4818_);
lean_inc_ref(v_visitedNames_4817_);
v_isSharedCheck_5546_ = !lean_is_exclusive(v_a_4705_);
if (v_isSharedCheck_5546_ == 0)
{
lean_object* v_unused_5547_; lean_object* v_unused_5548_; lean_object* v_unused_5549_; lean_object* v_unused_5550_; lean_object* v_unused_5551_; lean_object* v_unused_5552_; 
v_unused_5547_ = lean_ctor_get(v_a_4705_, 5);
lean_dec(v_unused_5547_);
v_unused_5548_ = lean_ctor_get(v_a_4705_, 4);
lean_dec(v_unused_5548_);
v_unused_5549_ = lean_ctor_get(v_a_4705_, 3);
lean_dec(v_unused_5549_);
v_unused_5550_ = lean_ctor_get(v_a_4705_, 2);
lean_dec(v_unused_5550_);
v_unused_5551_ = lean_ctor_get(v_a_4705_, 1);
lean_dec(v_unused_5551_);
v_unused_5552_ = lean_ctor_get(v_a_4705_, 0);
lean_dec(v_unused_5552_);
v___x_4828_ = v_a_4705_;
v_isShared_4829_ = v_isSharedCheck_5546_;
goto v_resetjp_4827_;
}
else
{
lean_dec(v_a_4705_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_5546_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4830_; lean_object* v___x_4832_; 
v___x_4830_ = l_Lean_NameHashSet_insert(v_visitedConstants_4820_, v_c_4703_);
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 3, v___x_4830_);
v___x_4832_ = v___x_4828_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_visitedNames_4817_);
lean_ctor_set(v_reuseFailAlloc_5545_, 1, v_visitedLevels_4818_);
lean_ctor_set(v_reuseFailAlloc_5545_, 2, v_visitedExprs_4819_);
lean_ctor_set(v_reuseFailAlloc_5545_, 3, v___x_4830_);
lean_ctor_set(v_reuseFailAlloc_5545_, 4, v_noMDataExprs_4821_);
lean_ctor_set(v_reuseFailAlloc_5545_, 5, v_recursorMap_4825_);
lean_ctor_set_uint8(v_reuseFailAlloc_5545_, sizeof(void*)*6, v_exportMData_4822_);
lean_ctor_set_uint8(v_reuseFailAlloc_5545_, sizeof(void*)*6 + 1, v_exportUnsafe_4823_);
lean_ctor_set_uint8(v_reuseFailAlloc_5545_, sizeof(void*)*6 + 2, v_ignoreMissing_4824_);
v___x_4832_ = v_reuseFailAlloc_5545_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
switch(lean_obj_tag(v_val_4815_))
{
case 0:
{
lean_object* v_val_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4937_; 
v_val_4833_ = lean_ctor_get(v_val_4815_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v_val_4815_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4835_ = v_val_4815_;
v_isShared_4836_ = v_isSharedCheck_4937_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_val_4833_);
lean_dec(v_val_4815_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4937_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v_toConstantVal_4837_; uint8_t v_isUnsafe_4838_; lean_object* v_name_4839_; lean_object* v_levelParams_4840_; lean_object* v_type_4841_; lean_object* v___x_4842_; 
v_toConstantVal_4837_ = lean_ctor_get(v_val_4833_, 0);
lean_inc_ref(v_toConstantVal_4837_);
v_isUnsafe_4838_ = lean_ctor_get_uint8(v_val_4833_, sizeof(void*)*1);
lean_dec_ref(v_val_4833_);
v_name_4839_ = lean_ctor_get(v_toConstantVal_4837_, 0);
lean_inc(v_name_4839_);
v_levelParams_4840_ = lean_ctor_get(v_toConstantVal_4837_, 1);
lean_inc(v_levelParams_4840_);
v_type_4841_ = lean_ctor_get(v_toConstantVal_4837_, 2);
lean_inc_ref_n(v_type_4841_, 2);
lean_dec_ref(v_toConstantVal_4837_);
v___x_4842_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4841_, v_a_4704_, v___x_4832_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v_a_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4936_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4845_ = v___x_4842_;
v_isShared_4846_ = v_isSharedCheck_4936_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_a_4843_);
lean_dec(v___x_4842_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4936_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v_snd_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4934_; 
v_snd_4847_ = lean_ctor_get(v_a_4843_, 1);
v_isSharedCheck_4934_ = !lean_is_exclusive(v_a_4843_);
if (v_isSharedCheck_4934_ == 0)
{
lean_object* v_unused_4935_; 
v_unused_4935_ = lean_ctor_get(v_a_4843_, 0);
lean_dec(v_unused_4935_);
v___x_4849_ = v_a_4843_;
v_isShared_4850_ = v_isSharedCheck_4934_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_snd_4847_);
lean_dec(v_a_4843_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4934_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4851_; 
v___x_4851_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4839_, v_a_4704_, v_snd_4847_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v_fst_4853_; lean_object* v_snd_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4925_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4851_, 1);
v_fst_4853_ = lean_ctor_get(v_a_4852_, 0);
v_snd_4854_ = lean_ctor_get(v_a_4852_, 1);
v_isSharedCheck_4925_ = !lean_is_exclusive(v_a_4852_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4856_ = v_a_4852_;
v_isShared_4857_ = v_isSharedCheck_4925_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_snd_4854_);
lean_inc(v_fst_4853_);
lean_dec(v_a_4852_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4925_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4858_; 
v___x_4858_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4840_, v_a_4704_, v_snd_4854_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; lean_object* v_fst_4860_; lean_object* v_snd_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4916_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
lean_inc(v_a_4859_);
lean_dec_ref_known(v___x_4858_, 1);
v_fst_4860_ = lean_ctor_get(v_a_4859_, 0);
v_snd_4861_ = lean_ctor_get(v_a_4859_, 1);
v_isSharedCheck_4916_ = !lean_is_exclusive(v_a_4859_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4863_ = v_a_4859_;
v_isShared_4864_ = v_isSharedCheck_4916_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_snd_4861_);
lean_inc(v_fst_4860_);
lean_dec(v_a_4859_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4916_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4865_; 
v___x_4865_ = l_LeanExport_dumpExpr(v_type_4841_, v_a_4704_, v_snd_4861_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v_a_4866_; lean_object* v_fst_4867_; lean_object* v_snd_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4907_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
lean_inc(v_a_4866_);
lean_dec_ref_known(v___x_4865_, 1);
v_fst_4867_ = lean_ctor_get(v_a_4866_, 0);
v_snd_4868_ = lean_ctor_get(v_a_4866_, 1);
v_isSharedCheck_4907_ = !lean_is_exclusive(v_a_4866_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4870_ = v_a_4866_;
v_isShared_4871_ = v_isSharedCheck_4907_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_snd_4868_);
lean_inc(v_fst_4867_);
lean_dec(v_a_4866_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4907_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4876_; 
v___x_4872_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__3));
v___x_4873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_4874_ = l_Lean_JsonNumber_fromNat(v_fst_4853_);
if (v_isShared_4846_ == 0)
{
lean_ctor_set_tag(v___x_4845_, 2);
lean_ctor_set(v___x_4845_, 0, v___x_4874_);
v___x_4876_ = v___x_4845_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4874_);
v___x_4876_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
lean_object* v___x_4878_; 
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 1, v___x_4876_);
lean_ctor_set(v___x_4870_, 0, v___x_4873_);
v___x_4878_ = v___x_4870_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v___x_4873_);
lean_ctor_set(v_reuseFailAlloc_4905_, 1, v___x_4876_);
v___x_4878_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
lean_object* v___x_4879_; lean_object* v___x_4881_; 
v___x_4879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 1, v_fst_4860_);
lean_ctor_set(v___x_4863_, 0, v___x_4879_);
v___x_4881_ = v___x_4863_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4879_);
lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_fst_4860_);
v___x_4881_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4885_; 
v___x_4882_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4883_ = l_Lean_JsonNumber_fromNat(v_fst_4867_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set_tag(v___x_4835_, 2);
lean_ctor_set(v___x_4835_, 0, v___x_4883_);
v___x_4885_ = v___x_4835_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4883_);
v___x_4885_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
lean_object* v___x_4887_; 
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 1, v___x_4885_);
lean_ctor_set(v___x_4856_, 0, v___x_4882_);
v___x_4887_ = v___x_4856_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4882_);
lean_ctor_set(v_reuseFailAlloc_4902_, 1, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6));
v___x_4889_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4889_, 0, v_isUnsafe_4838_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v___x_4889_);
lean_ctor_set(v___x_4849_, 0, v___x_4888_);
v___x_4891_ = v___x_4849_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v___x_4888_);
lean_ctor_set(v_reuseFailAlloc_4901_, 1, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4892_ = lean_box(0);
v___x_4893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4891_);
lean_ctor_set(v___x_4893_, 1, v___x_4892_);
v___x_4894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4887_);
lean_ctor_set(v___x_4894_, 1, v___x_4893_);
v___x_4895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4881_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
v___x_4896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4878_);
lean_ctor_set(v___x_4896_, 1, v___x_4895_);
v___x_4897_ = l_Lean_Json_mkObj(v___x_4896_);
lean_dec_ref_known(v___x_4896_, 2);
v___x_4898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4872_);
lean_ctor_set(v___x_4898_, 1, v___x_4897_);
v___x_4899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4898_);
lean_ctor_set(v___x_4899_, 1, v___x_4892_);
v___x_4900_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4899_, v_snd_4868_);
lean_dec_ref_known(v___x_4899_, 2);
return v___x_4900_;
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
lean_object* v_a_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4915_; 
lean_del_object(v___x_4863_);
lean_dec(v_fst_4860_);
lean_del_object(v___x_4856_);
lean_dec(v_fst_4853_);
lean_del_object(v___x_4849_);
lean_del_object(v___x_4845_);
lean_del_object(v___x_4835_);
v_a_4908_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4910_ = v___x_4865_;
v_isShared_4911_ = v_isSharedCheck_4915_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_a_4908_);
lean_dec(v___x_4865_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4915_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4913_; 
if (v_isShared_4911_ == 0)
{
v___x_4913_ = v___x_4910_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_a_4908_);
v___x_4913_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
return v___x_4913_;
}
}
}
}
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_del_object(v___x_4856_);
lean_dec(v_fst_4853_);
lean_del_object(v___x_4849_);
lean_del_object(v___x_4845_);
lean_dec_ref(v_type_4841_);
lean_del_object(v___x_4835_);
v_a_4917_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4858_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4858_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
}
else
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4933_; 
lean_del_object(v___x_4849_);
lean_del_object(v___x_4845_);
lean_dec_ref(v_type_4841_);
lean_dec(v_levelParams_4840_);
lean_del_object(v___x_4835_);
v_a_4926_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4928_ = v___x_4851_;
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4851_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4931_; 
if (v_isShared_4929_ == 0)
{
v___x_4931_ = v___x_4928_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_a_4926_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_type_4841_);
lean_dec(v_levelParams_4840_);
lean_dec(v_name_4839_);
lean_del_object(v___x_4835_);
return v___x_4842_;
}
}
}
case 1:
{
lean_object* v_val_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_5109_; 
v_val_4938_ = lean_ctor_get(v_val_4815_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v_val_4815_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_4940_ = v_val_4815_;
v_isShared_4941_ = v_isSharedCheck_5109_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_val_4938_);
lean_dec(v_val_4815_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_5109_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v_toConstantVal_4942_; lean_object* v_value_4943_; lean_object* v_hints_4944_; uint8_t v_safety_4945_; lean_object* v_all_4946_; lean_object* v_name_4947_; lean_object* v_levelParams_4948_; lean_object* v_type_4949_; lean_object* v___x_4950_; 
v_toConstantVal_4942_ = lean_ctor_get(v_val_4938_, 0);
lean_inc_ref(v_toConstantVal_4942_);
v_value_4943_ = lean_ctor_get(v_val_4938_, 1);
lean_inc_ref(v_value_4943_);
v_hints_4944_ = lean_ctor_get(v_val_4938_, 2);
lean_inc(v_hints_4944_);
v_safety_4945_ = lean_ctor_get_uint8(v_val_4938_, sizeof(void*)*4);
v_all_4946_ = lean_ctor_get(v_val_4938_, 3);
lean_inc(v_all_4946_);
lean_dec_ref(v_val_4938_);
v_name_4947_ = lean_ctor_get(v_toConstantVal_4942_, 0);
lean_inc(v_name_4947_);
v_levelParams_4948_ = lean_ctor_get(v_toConstantVal_4942_, 1);
lean_inc(v_levelParams_4948_);
v_type_4949_ = lean_ctor_get(v_toConstantVal_4942_, 2);
lean_inc_ref_n(v_type_4949_, 2);
lean_dec_ref(v_toConstantVal_4942_);
v___x_4950_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4949_, v_a_4704_, v___x_4832_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_5108_; 
v_a_4951_ = lean_ctor_get(v___x_4950_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_4953_ = v___x_4950_;
v_isShared_4954_ = v_isSharedCheck_5108_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v___x_4950_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_5108_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v_snd_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_5106_; 
v_snd_4955_ = lean_ctor_get(v_a_4951_, 1);
v_isSharedCheck_5106_ = !lean_is_exclusive(v_a_4951_);
if (v_isSharedCheck_5106_ == 0)
{
lean_object* v_unused_5107_; 
v_unused_5107_ = lean_ctor_get(v_a_4951_, 0);
lean_dec(v_unused_5107_);
v___x_4957_ = v_a_4951_;
v_isShared_4958_ = v_isSharedCheck_5106_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_snd_4955_);
lean_dec(v_a_4951_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_5106_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4959_; 
lean_inc_ref(v_value_4943_);
v___x_4959_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_4943_, v_a_4704_, v_snd_4955_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_5105_; 
v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_4962_ = v___x_4959_;
v_isShared_4963_ = v_isSharedCheck_5105_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4959_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_5105_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v_snd_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_5103_; 
v_snd_4964_ = lean_ctor_get(v_a_4960_, 1);
v_isSharedCheck_5103_ = !lean_is_exclusive(v_a_4960_);
if (v_isSharedCheck_5103_ == 0)
{
lean_object* v_unused_5104_; 
v_unused_5104_ = lean_ctor_get(v_a_4960_, 0);
lean_dec(v_unused_5104_);
v___x_4966_ = v_a_4960_;
v_isShared_4967_ = v_isSharedCheck_5103_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_snd_4964_);
lean_dec(v_a_4960_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_5103_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4968_; 
v___x_4968_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4947_, v_a_4704_, v_snd_4964_);
if (lean_obj_tag(v___x_4968_) == 0)
{
lean_object* v_a_4969_; lean_object* v_fst_4970_; lean_object* v_snd_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_5094_; 
v_a_4969_ = lean_ctor_get(v___x_4968_, 0);
lean_inc(v_a_4969_);
lean_dec_ref_known(v___x_4968_, 1);
v_fst_4970_ = lean_ctor_get(v_a_4969_, 0);
v_snd_4971_ = lean_ctor_get(v_a_4969_, 1);
v_isSharedCheck_5094_ = !lean_is_exclusive(v_a_4969_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_4973_ = v_a_4969_;
v_isShared_4974_ = v_isSharedCheck_5094_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_snd_4971_);
lean_inc(v_fst_4970_);
lean_dec(v_a_4969_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_5094_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4975_; 
v___x_4975_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4948_, v_a_4704_, v_snd_4971_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v_a_4976_; lean_object* v_fst_4977_; lean_object* v_snd_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_5085_; 
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_a_4976_);
lean_dec_ref_known(v___x_4975_, 1);
v_fst_4977_ = lean_ctor_get(v_a_4976_, 0);
v_snd_4978_ = lean_ctor_get(v_a_4976_, 1);
v_isSharedCheck_5085_ = !lean_is_exclusive(v_a_4976_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_4980_ = v_a_4976_;
v_isShared_4981_ = v_isSharedCheck_5085_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_snd_4978_);
lean_inc(v_fst_4977_);
lean_dec(v_a_4976_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_5085_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4982_; 
v___x_4982_ = l_LeanExport_dumpExpr(v_type_4949_, v_a_4704_, v_snd_4978_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v_fst_4984_; lean_object* v_snd_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_5076_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v___x_4982_, 1);
v_fst_4984_ = lean_ctor_get(v_a_4983_, 0);
v_snd_4985_ = lean_ctor_get(v_a_4983_, 1);
v_isSharedCheck_5076_ = !lean_is_exclusive(v_a_4983_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_4987_ = v_a_4983_;
v_isShared_4988_ = v_isSharedCheck_5076_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_snd_4985_);
lean_inc(v_fst_4984_);
lean_dec(v_a_4983_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_5076_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4989_; 
v___x_4989_ = l_LeanExport_dumpExpr(v_value_4943_, v_a_4704_, v_snd_4985_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v_a_4990_; lean_object* v_fst_4991_; lean_object* v_snd_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_5067_; 
v_a_4990_ = lean_ctor_get(v___x_4989_, 0);
lean_inc(v_a_4990_);
lean_dec_ref_known(v___x_4989_, 1);
v_fst_4991_ = lean_ctor_get(v_a_4990_, 0);
v_snd_4992_ = lean_ctor_get(v_a_4990_, 1);
v_isSharedCheck_5067_ = !lean_is_exclusive(v_a_4990_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_4994_ = v_a_4990_;
v_isShared_4995_ = v_isSharedCheck_5067_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_snd_4992_);
lean_inc(v_fst_4991_);
lean_dec(v_a_4990_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_5067_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4996_; 
v___x_4996_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_4946_, v_a_4704_, v_snd_4992_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v_a_4997_; lean_object* v_fst_4998_; lean_object* v_snd_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5058_; 
v_a_4997_ = lean_ctor_get(v___x_4996_, 0);
lean_inc(v_a_4997_);
lean_dec_ref_known(v___x_4996_, 1);
v_fst_4998_ = lean_ctor_get(v_a_4997_, 0);
v_snd_4999_ = lean_ctor_get(v_a_4997_, 1);
v_isSharedCheck_5058_ = !lean_is_exclusive(v_a_4997_);
if (v_isSharedCheck_5058_ == 0)
{
v___x_5001_ = v_a_4997_;
v_isShared_5002_ = v_isSharedCheck_5058_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_snd_4999_);
lean_inc(v_fst_4998_);
lean_dec(v_a_4997_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5058_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5007_; 
v___x_5003_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__4));
v___x_5004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_5005_ = l_Lean_JsonNumber_fromNat(v_fst_4970_);
if (v_isShared_4963_ == 0)
{
lean_ctor_set_tag(v___x_4962_, 2);
lean_ctor_set(v___x_4962_, 0, v___x_5005_);
v___x_5007_ = v___x_4962_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___x_5005_);
v___x_5007_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
lean_object* v___x_5009_; 
if (v_isShared_5002_ == 0)
{
lean_ctor_set(v___x_5001_, 1, v___x_5007_);
lean_ctor_set(v___x_5001_, 0, v___x_5004_);
v___x_5009_ = v___x_5001_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5004_);
lean_ctor_set(v_reuseFailAlloc_5056_, 1, v___x_5007_);
v___x_5009_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5012_; 
v___x_5010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_4995_ == 0)
{
lean_ctor_set(v___x_4994_, 1, v_fst_4977_);
lean_ctor_set(v___x_4994_, 0, v___x_5010_);
v___x_5012_ = v___x_4994_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5010_);
lean_ctor_set(v_reuseFailAlloc_5055_, 1, v_fst_4977_);
v___x_5012_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5016_; 
v___x_5013_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5014_ = l_Lean_JsonNumber_fromNat(v_fst_4984_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set_tag(v___x_4953_, 2);
lean_ctor_set(v___x_4953_, 0, v___x_5014_);
v___x_5016_ = v___x_4953_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5014_);
v___x_5016_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
lean_object* v___x_5018_; 
if (v_isShared_4988_ == 0)
{
lean_ctor_set(v___x_4987_, 1, v___x_5016_);
lean_ctor_set(v___x_4987_, 0, v___x_5013_);
v___x_5018_ = v___x_4987_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v___x_5013_);
lean_ctor_set(v_reuseFailAlloc_5053_, 1, v___x_5016_);
v___x_5018_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5022_; 
v___x_5019_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5020_ = l_Lean_JsonNumber_fromNat(v_fst_4991_);
if (v_isShared_4941_ == 0)
{
lean_ctor_set_tag(v___x_4940_, 2);
lean_ctor_set(v___x_4940_, 0, v___x_5020_);
v___x_5022_ = v___x_4940_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v___x_5020_);
v___x_5022_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
lean_object* v___x_5024_; 
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 1, v___x_5022_);
lean_ctor_set(v___x_4980_, 0, v___x_5019_);
v___x_5024_ = v___x_4980_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v___x_5019_);
lean_ctor_set(v_reuseFailAlloc_5051_, 1, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5028_; 
v___x_5025_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__5));
v___x_5026_ = l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(v_hints_4944_);
lean_dec(v_hints_4944_);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 1, v___x_5026_);
lean_ctor_set(v___x_4973_, 0, v___x_5025_);
v___x_5028_ = v___x_4973_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5025_);
lean_ctor_set(v_reuseFailAlloc_5050_, 1, v___x_5026_);
v___x_5028_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5032_; 
v___x_5029_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__6));
v___x_5030_ = l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(v_safety_4945_);
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 1, v___x_5030_);
lean_ctor_set(v___x_4966_, 0, v___x_5029_);
v___x_5032_ = v___x_4966_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5029_);
lean_ctor_set(v_reuseFailAlloc_5049_, 1, v___x_5030_);
v___x_5032_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
lean_object* v___x_5033_; lean_object* v___x_5035_; 
v___x_5033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 1, v_fst_4998_);
lean_ctor_set(v___x_4957_, 0, v___x_5033_);
v___x_5035_ = v___x_4957_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5033_);
lean_ctor_set(v_reuseFailAlloc_5048_, 1, v_fst_4998_);
v___x_5035_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5036_ = lean_box(0);
v___x_5037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5035_);
lean_ctor_set(v___x_5037_, 1, v___x_5036_);
v___x_5038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5032_);
lean_ctor_set(v___x_5038_, 1, v___x_5037_);
v___x_5039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5039_, 0, v___x_5028_);
lean_ctor_set(v___x_5039_, 1, v___x_5038_);
v___x_5040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5024_);
lean_ctor_set(v___x_5040_, 1, v___x_5039_);
v___x_5041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5041_, 0, v___x_5018_);
lean_ctor_set(v___x_5041_, 1, v___x_5040_);
v___x_5042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5042_, 0, v___x_5012_);
lean_ctor_set(v___x_5042_, 1, v___x_5041_);
v___x_5043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5009_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
v___x_5044_ = l_Lean_Json_mkObj(v___x_5043_);
lean_dec_ref_known(v___x_5043_, 2);
v___x_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5003_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
v___x_5046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5046_, 0, v___x_5045_);
lean_ctor_set(v___x_5046_, 1, v___x_5036_);
v___x_5047_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5046_, v_snd_4999_);
lean_dec_ref_known(v___x_5046_, 2);
return v___x_5047_;
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
lean_object* v_a_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5066_; 
lean_del_object(v___x_4994_);
lean_dec(v_fst_4991_);
lean_del_object(v___x_4987_);
lean_dec(v_fst_4984_);
lean_del_object(v___x_4980_);
lean_dec(v_fst_4977_);
lean_del_object(v___x_4973_);
lean_dec(v_fst_4970_);
lean_del_object(v___x_4966_);
lean_del_object(v___x_4962_);
lean_del_object(v___x_4957_);
lean_del_object(v___x_4953_);
lean_dec(v_hints_4944_);
lean_del_object(v___x_4940_);
v_a_5059_ = lean_ctor_get(v___x_4996_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5061_ = v___x_4996_;
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_a_5059_);
lean_dec(v___x_4996_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5064_; 
if (v_isShared_5062_ == 0)
{
v___x_5064_ = v___x_5061_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5059_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_del_object(v___x_4987_);
lean_dec(v_fst_4984_);
lean_del_object(v___x_4980_);
lean_dec(v_fst_4977_);
lean_del_object(v___x_4973_);
lean_dec(v_fst_4970_);
lean_del_object(v___x_4966_);
lean_del_object(v___x_4962_);
lean_del_object(v___x_4957_);
lean_del_object(v___x_4953_);
lean_dec(v_all_4946_);
lean_dec(v_hints_4944_);
lean_del_object(v___x_4940_);
v_a_5068_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_4989_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_4989_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_del_object(v___x_4980_);
lean_dec(v_fst_4977_);
lean_del_object(v___x_4973_);
lean_dec(v_fst_4970_);
lean_del_object(v___x_4966_);
lean_del_object(v___x_4962_);
lean_del_object(v___x_4957_);
lean_del_object(v___x_4953_);
lean_dec(v_all_4946_);
lean_dec(v_hints_4944_);
lean_dec_ref(v_value_4943_);
lean_del_object(v___x_4940_);
v_a_5077_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_4982_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_4982_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
}
else
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
lean_del_object(v___x_4973_);
lean_dec(v_fst_4970_);
lean_del_object(v___x_4966_);
lean_del_object(v___x_4962_);
lean_del_object(v___x_4957_);
lean_del_object(v___x_4953_);
lean_dec_ref(v_type_4949_);
lean_dec(v_all_4946_);
lean_dec(v_hints_4944_);
lean_dec_ref(v_value_4943_);
lean_del_object(v___x_4940_);
v_a_5086_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_4975_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_4975_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
}
else
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
lean_del_object(v___x_4966_);
lean_del_object(v___x_4962_);
lean_del_object(v___x_4957_);
lean_del_object(v___x_4953_);
lean_dec_ref(v_type_4949_);
lean_dec(v_levelParams_4948_);
lean_dec(v_all_4946_);
lean_dec(v_hints_4944_);
lean_dec_ref(v_value_4943_);
lean_del_object(v___x_4940_);
v_a_5095_ = lean_ctor_get(v___x_4968_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_4968_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_4968_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_4968_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4957_);
lean_del_object(v___x_4953_);
lean_dec_ref(v_type_4949_);
lean_dec(v_levelParams_4948_);
lean_dec(v_name_4947_);
lean_dec(v_all_4946_);
lean_dec(v_hints_4944_);
lean_dec_ref(v_value_4943_);
lean_del_object(v___x_4940_);
return v___x_4959_;
}
}
}
}
else
{
lean_dec_ref(v_type_4949_);
lean_dec(v_levelParams_4948_);
lean_dec(v_name_4947_);
lean_dec(v_all_4946_);
lean_dec(v_hints_4944_);
lean_dec_ref(v_value_4943_);
lean_del_object(v___x_4940_);
return v___x_4950_;
}
}
}
case 2:
{
lean_object* v_val_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5271_; 
v_val_5110_ = lean_ctor_get(v_val_4815_, 0);
v_isSharedCheck_5271_ = !lean_is_exclusive(v_val_4815_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5112_ = v_val_4815_;
v_isShared_5113_ = v_isSharedCheck_5271_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_val_5110_);
lean_dec(v_val_4815_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5271_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v_toConstantVal_5114_; lean_object* v_value_5115_; lean_object* v_all_5116_; lean_object* v_name_5117_; lean_object* v_levelParams_5118_; lean_object* v_type_5119_; lean_object* v___x_5120_; 
v_toConstantVal_5114_ = lean_ctor_get(v_val_5110_, 0);
lean_inc_ref(v_toConstantVal_5114_);
v_value_5115_ = lean_ctor_get(v_val_5110_, 1);
lean_inc_ref(v_value_5115_);
v_all_5116_ = lean_ctor_get(v_val_5110_, 2);
lean_inc(v_all_5116_);
lean_dec_ref(v_val_5110_);
v_name_5117_ = lean_ctor_get(v_toConstantVal_5114_, 0);
lean_inc(v_name_5117_);
v_levelParams_5118_ = lean_ctor_get(v_toConstantVal_5114_, 1);
lean_inc(v_levelParams_5118_);
v_type_5119_ = lean_ctor_get(v_toConstantVal_5114_, 2);
lean_inc_ref_n(v_type_5119_, 2);
lean_dec_ref(v_toConstantVal_5114_);
v___x_5120_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5119_, v_a_4704_, v___x_4832_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5270_; 
v_a_5121_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5123_ = v___x_5120_;
v_isShared_5124_ = v_isSharedCheck_5270_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5120_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5270_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v_snd_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5268_; 
v_snd_5125_ = lean_ctor_get(v_a_5121_, 1);
v_isSharedCheck_5268_ = !lean_is_exclusive(v_a_5121_);
if (v_isSharedCheck_5268_ == 0)
{
lean_object* v_unused_5269_; 
v_unused_5269_ = lean_ctor_get(v_a_5121_, 0);
lean_dec(v_unused_5269_);
v___x_5127_ = v_a_5121_;
v_isShared_5128_ = v_isSharedCheck_5268_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_snd_5125_);
lean_dec(v_a_5121_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5268_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5129_; 
lean_inc_ref(v_value_5115_);
v___x_5129_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5115_, v_a_4704_, v_snd_5125_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5267_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5132_ = v___x_5129_;
v_isShared_5133_ = v_isSharedCheck_5267_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5129_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5267_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v_snd_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5265_; 
v_snd_5134_ = lean_ctor_get(v_a_5130_, 1);
v_isSharedCheck_5265_ = !lean_is_exclusive(v_a_5130_);
if (v_isSharedCheck_5265_ == 0)
{
lean_object* v_unused_5266_; 
v_unused_5266_ = lean_ctor_get(v_a_5130_, 0);
lean_dec(v_unused_5266_);
v___x_5136_ = v_a_5130_;
v_isShared_5137_ = v_isSharedCheck_5265_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_snd_5134_);
lean_dec(v_a_5130_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5265_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5138_; 
v___x_5138_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5117_, v_a_4704_, v_snd_5134_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v_a_5139_; lean_object* v_fst_5140_; lean_object* v_snd_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5256_; 
v_a_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc(v_a_5139_);
lean_dec_ref_known(v___x_5138_, 1);
v_fst_5140_ = lean_ctor_get(v_a_5139_, 0);
v_snd_5141_ = lean_ctor_get(v_a_5139_, 1);
v_isSharedCheck_5256_ = !lean_is_exclusive(v_a_5139_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5143_ = v_a_5139_;
v_isShared_5144_ = v_isSharedCheck_5256_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_snd_5141_);
lean_inc(v_fst_5140_);
lean_dec(v_a_5139_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5256_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v___x_5145_; 
v___x_5145_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5118_, v_a_4704_, v_snd_5141_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; lean_object* v_fst_5147_; lean_object* v_snd_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5247_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5146_);
lean_dec_ref_known(v___x_5145_, 1);
v_fst_5147_ = lean_ctor_get(v_a_5146_, 0);
v_snd_5148_ = lean_ctor_get(v_a_5146_, 1);
v_isSharedCheck_5247_ = !lean_is_exclusive(v_a_5146_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5150_ = v_a_5146_;
v_isShared_5151_ = v_isSharedCheck_5247_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_snd_5148_);
lean_inc(v_fst_5147_);
lean_dec(v_a_5146_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5247_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5152_; 
v___x_5152_ = l_LeanExport_dumpExpr(v_type_5119_, v_a_4704_, v_snd_5148_);
if (lean_obj_tag(v___x_5152_) == 0)
{
lean_object* v_a_5153_; lean_object* v_fst_5154_; lean_object* v_snd_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5238_; 
v_a_5153_ = lean_ctor_get(v___x_5152_, 0);
lean_inc(v_a_5153_);
lean_dec_ref_known(v___x_5152_, 1);
v_fst_5154_ = lean_ctor_get(v_a_5153_, 0);
v_snd_5155_ = lean_ctor_get(v_a_5153_, 1);
v_isSharedCheck_5238_ = !lean_is_exclusive(v_a_5153_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5157_ = v_a_5153_;
v_isShared_5158_ = v_isSharedCheck_5238_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_snd_5155_);
lean_inc(v_fst_5154_);
lean_dec(v_a_5153_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5238_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v___x_5159_; 
v___x_5159_ = l_LeanExport_dumpExpr(v_value_5115_, v_a_4704_, v_snd_5155_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; lean_object* v_fst_5161_; lean_object* v_snd_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5229_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_a_5160_);
lean_dec_ref_known(v___x_5159_, 1);
v_fst_5161_ = lean_ctor_get(v_a_5160_, 0);
v_snd_5162_ = lean_ctor_get(v_a_5160_, 1);
v_isSharedCheck_5229_ = !lean_is_exclusive(v_a_5160_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5164_ = v_a_5160_;
v_isShared_5165_ = v_isSharedCheck_5229_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_snd_5162_);
lean_inc(v_fst_5161_);
lean_dec(v_a_5160_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5229_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5166_; 
v___x_5166_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5116_, v_a_4704_, v_snd_5162_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v_fst_5168_; lean_object* v_snd_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5220_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref_known(v___x_5166_, 1);
v_fst_5168_ = lean_ctor_get(v_a_5167_, 0);
v_snd_5169_ = lean_ctor_get(v_a_5167_, 1);
v_isSharedCheck_5220_ = !lean_is_exclusive(v_a_5167_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5171_ = v_a_5167_;
v_isShared_5172_ = v_isSharedCheck_5220_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_snd_5169_);
lean_inc(v_fst_5168_);
lean_dec(v_a_5167_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5220_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5177_; 
v___x_5173_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__7));
v___x_5174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_5175_ = l_Lean_JsonNumber_fromNat(v_fst_5140_);
if (v_isShared_5133_ == 0)
{
lean_ctor_set_tag(v___x_5132_, 2);
lean_ctor_set(v___x_5132_, 0, v___x_5175_);
v___x_5177_ = v___x_5132_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v___x_5175_);
v___x_5177_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
lean_object* v___x_5179_; 
if (v_isShared_5172_ == 0)
{
lean_ctor_set(v___x_5171_, 1, v___x_5177_);
lean_ctor_set(v___x_5171_, 0, v___x_5174_);
v___x_5179_ = v___x_5171_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5174_);
lean_ctor_set(v_reuseFailAlloc_5218_, 1, v___x_5177_);
v___x_5179_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
lean_object* v___x_5180_; lean_object* v___x_5182_; 
v___x_5180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_5165_ == 0)
{
lean_ctor_set(v___x_5164_, 1, v_fst_5147_);
lean_ctor_set(v___x_5164_, 0, v___x_5180_);
v___x_5182_ = v___x_5164_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v___x_5180_);
lean_ctor_set(v_reuseFailAlloc_5217_, 1, v_fst_5147_);
v___x_5182_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5186_; 
v___x_5183_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5184_ = l_Lean_JsonNumber_fromNat(v_fst_5154_);
if (v_isShared_5124_ == 0)
{
lean_ctor_set_tag(v___x_5123_, 2);
lean_ctor_set(v___x_5123_, 0, v___x_5184_);
v___x_5186_ = v___x_5123_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v___x_5184_);
v___x_5186_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
lean_object* v___x_5188_; 
if (v_isShared_5158_ == 0)
{
lean_ctor_set(v___x_5157_, 1, v___x_5186_);
lean_ctor_set(v___x_5157_, 0, v___x_5183_);
v___x_5188_ = v___x_5157_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v___x_5183_);
lean_ctor_set(v_reuseFailAlloc_5215_, 1, v___x_5186_);
v___x_5188_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5192_; 
v___x_5189_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5190_ = l_Lean_JsonNumber_fromNat(v_fst_5161_);
if (v_isShared_5113_ == 0)
{
lean_ctor_set(v___x_5112_, 0, v___x_5190_);
v___x_5192_ = v___x_5112_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v___x_5190_);
v___x_5192_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
lean_object* v___x_5194_; 
if (v_isShared_5151_ == 0)
{
lean_ctor_set(v___x_5150_, 1, v___x_5192_);
lean_ctor_set(v___x_5150_, 0, v___x_5189_);
v___x_5194_ = v___x_5150_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5189_);
lean_ctor_set(v_reuseFailAlloc_5213_, 1, v___x_5192_);
v___x_5194_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
lean_object* v___x_5195_; lean_object* v___x_5197_; 
v___x_5195_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
if (v_isShared_5144_ == 0)
{
lean_ctor_set(v___x_5143_, 1, v_fst_5168_);
lean_ctor_set(v___x_5143_, 0, v___x_5195_);
v___x_5197_ = v___x_5143_;
goto v_reusejp_5196_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v___x_5195_);
lean_ctor_set(v_reuseFailAlloc_5212_, 1, v_fst_5168_);
v___x_5197_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5196_;
}
v_reusejp_5196_:
{
lean_object* v___x_5198_; lean_object* v___x_5200_; 
v___x_5198_ = lean_box(0);
if (v_isShared_5128_ == 0)
{
lean_ctor_set_tag(v___x_5127_, 1);
lean_ctor_set(v___x_5127_, 1, v___x_5198_);
lean_ctor_set(v___x_5127_, 0, v___x_5197_);
v___x_5200_ = v___x_5127_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v___x_5197_);
lean_ctor_set(v_reuseFailAlloc_5211_, 1, v___x_5198_);
v___x_5200_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5207_; 
v___x_5201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5194_);
lean_ctor_set(v___x_5201_, 1, v___x_5200_);
v___x_5202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5188_);
lean_ctor_set(v___x_5202_, 1, v___x_5201_);
v___x_5203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5182_);
lean_ctor_set(v___x_5203_, 1, v___x_5202_);
v___x_5204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5179_);
lean_ctor_set(v___x_5204_, 1, v___x_5203_);
v___x_5205_ = l_Lean_Json_mkObj(v___x_5204_);
lean_dec_ref_known(v___x_5204_, 2);
if (v_isShared_5137_ == 0)
{
lean_ctor_set(v___x_5136_, 1, v___x_5205_);
lean_ctor_set(v___x_5136_, 0, v___x_5173_);
v___x_5207_ = v___x_5136_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___x_5173_);
lean_ctor_set(v_reuseFailAlloc_5210_, 1, v___x_5205_);
v___x_5207_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
lean_object* v___x_5208_; lean_object* v___x_5209_; 
v___x_5208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5208_, 0, v___x_5207_);
lean_ctor_set(v___x_5208_, 1, v___x_5198_);
v___x_5209_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5208_, v_snd_5169_);
lean_dec_ref_known(v___x_5208_, 2);
return v___x_5209_;
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
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5228_; 
lean_del_object(v___x_5164_);
lean_dec(v_fst_5161_);
lean_del_object(v___x_5157_);
lean_dec(v_fst_5154_);
lean_del_object(v___x_5150_);
lean_dec(v_fst_5147_);
lean_del_object(v___x_5143_);
lean_dec(v_fst_5140_);
lean_del_object(v___x_5136_);
lean_del_object(v___x_5132_);
lean_del_object(v___x_5127_);
lean_del_object(v___x_5123_);
lean_del_object(v___x_5112_);
v_a_5221_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5166_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5166_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5224_ == 0)
{
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
return v___x_5226_;
}
}
}
}
}
else
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5237_; 
lean_del_object(v___x_5157_);
lean_dec(v_fst_5154_);
lean_del_object(v___x_5150_);
lean_dec(v_fst_5147_);
lean_del_object(v___x_5143_);
lean_dec(v_fst_5140_);
lean_del_object(v___x_5136_);
lean_del_object(v___x_5132_);
lean_del_object(v___x_5127_);
lean_del_object(v___x_5123_);
lean_dec(v_all_5116_);
lean_del_object(v___x_5112_);
v_a_5230_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5232_ = v___x_5159_;
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5159_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5235_; 
if (v_isShared_5233_ == 0)
{
v___x_5235_ = v___x_5232_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_a_5230_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
}
}
}
else
{
lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5246_; 
lean_del_object(v___x_5150_);
lean_dec(v_fst_5147_);
lean_del_object(v___x_5143_);
lean_dec(v_fst_5140_);
lean_del_object(v___x_5136_);
lean_del_object(v___x_5132_);
lean_del_object(v___x_5127_);
lean_del_object(v___x_5123_);
lean_dec(v_all_5116_);
lean_dec_ref(v_value_5115_);
lean_del_object(v___x_5112_);
v_a_5239_ = lean_ctor_get(v___x_5152_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5152_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5241_ = v___x_5152_;
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5152_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
}
}
else
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5255_; 
lean_del_object(v___x_5143_);
lean_dec(v_fst_5140_);
lean_del_object(v___x_5136_);
lean_del_object(v___x_5132_);
lean_del_object(v___x_5127_);
lean_del_object(v___x_5123_);
lean_dec_ref(v_type_5119_);
lean_dec(v_all_5116_);
lean_dec_ref(v_value_5115_);
lean_del_object(v___x_5112_);
v_a_5248_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5250_ = v___x_5145_;
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5145_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
}
else
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5264_; 
lean_del_object(v___x_5136_);
lean_del_object(v___x_5132_);
lean_del_object(v___x_5127_);
lean_del_object(v___x_5123_);
lean_dec_ref(v_type_5119_);
lean_dec(v_levelParams_5118_);
lean_dec(v_all_5116_);
lean_dec_ref(v_value_5115_);
lean_del_object(v___x_5112_);
v_a_5257_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5259_ = v___x_5138_;
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5138_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5262_; 
if (v_isShared_5260_ == 0)
{
v___x_5262_ = v___x_5259_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5257_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5127_);
lean_del_object(v___x_5123_);
lean_dec_ref(v_type_5119_);
lean_dec(v_levelParams_5118_);
lean_dec(v_name_5117_);
lean_dec(v_all_5116_);
lean_dec_ref(v_value_5115_);
lean_del_object(v___x_5112_);
return v___x_5129_;
}
}
}
}
else
{
lean_dec_ref(v_type_5119_);
lean_dec(v_levelParams_5118_);
lean_dec(v_name_5117_);
lean_dec(v_all_5116_);
lean_dec_ref(v_value_5115_);
lean_del_object(v___x_5112_);
return v___x_5120_;
}
}
}
case 3:
{
lean_object* v_val_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5438_; 
v_val_5272_ = lean_ctor_get(v_val_4815_, 0);
v_isSharedCheck_5438_ = !lean_is_exclusive(v_val_4815_);
if (v_isSharedCheck_5438_ == 0)
{
v___x_5274_ = v_val_4815_;
v_isShared_5275_ = v_isSharedCheck_5438_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_val_5272_);
lean_dec(v_val_4815_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5438_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v_toConstantVal_5276_; lean_object* v_value_5277_; uint8_t v_isUnsafe_5278_; lean_object* v_all_5279_; lean_object* v_name_5280_; lean_object* v_levelParams_5281_; lean_object* v_type_5282_; lean_object* v___x_5283_; 
v_toConstantVal_5276_ = lean_ctor_get(v_val_5272_, 0);
lean_inc_ref(v_toConstantVal_5276_);
v_value_5277_ = lean_ctor_get(v_val_5272_, 1);
lean_inc_ref(v_value_5277_);
v_isUnsafe_5278_ = lean_ctor_get_uint8(v_val_5272_, sizeof(void*)*3);
v_all_5279_ = lean_ctor_get(v_val_5272_, 2);
lean_inc(v_all_5279_);
lean_dec_ref(v_val_5272_);
v_name_5280_ = lean_ctor_get(v_toConstantVal_5276_, 0);
lean_inc(v_name_5280_);
v_levelParams_5281_ = lean_ctor_get(v_toConstantVal_5276_, 1);
lean_inc(v_levelParams_5281_);
v_type_5282_ = lean_ctor_get(v_toConstantVal_5276_, 2);
lean_inc_ref_n(v_type_5282_, 2);
lean_dec_ref(v_toConstantVal_5276_);
v___x_5283_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5282_, v_a_4704_, v___x_4832_);
if (lean_obj_tag(v___x_5283_) == 0)
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5437_; 
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5437_ == 0)
{
v___x_5286_ = v___x_5283_;
v_isShared_5287_ = v_isSharedCheck_5437_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5283_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5437_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v_snd_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5435_; 
v_snd_5288_ = lean_ctor_get(v_a_5284_, 1);
v_isSharedCheck_5435_ = !lean_is_exclusive(v_a_5284_);
if (v_isSharedCheck_5435_ == 0)
{
lean_object* v_unused_5436_; 
v_unused_5436_ = lean_ctor_get(v_a_5284_, 0);
lean_dec(v_unused_5436_);
v___x_5290_ = v_a_5284_;
v_isShared_5291_ = v_isSharedCheck_5435_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_snd_5288_);
lean_dec(v_a_5284_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5435_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5292_; 
lean_inc_ref(v_value_5277_);
v___x_5292_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5277_, v_a_4704_, v_snd_5288_);
if (lean_obj_tag(v___x_5292_) == 0)
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5434_; 
v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5295_ = v___x_5292_;
v_isShared_5296_ = v_isSharedCheck_5434_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5292_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5434_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v_snd_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5432_; 
v_snd_5297_ = lean_ctor_get(v_a_5293_, 1);
v_isSharedCheck_5432_ = !lean_is_exclusive(v_a_5293_);
if (v_isSharedCheck_5432_ == 0)
{
lean_object* v_unused_5433_; 
v_unused_5433_ = lean_ctor_get(v_a_5293_, 0);
lean_dec(v_unused_5433_);
v___x_5299_ = v_a_5293_;
v_isShared_5300_ = v_isSharedCheck_5432_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_snd_5297_);
lean_dec(v_a_5293_);
v___x_5299_ = lean_box(0);
v_isShared_5300_ = v_isSharedCheck_5432_;
goto v_resetjp_5298_;
}
v_resetjp_5298_:
{
lean_object* v___x_5301_; 
v___x_5301_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5280_, v_a_4704_, v_snd_5297_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v_a_5302_; lean_object* v_fst_5303_; lean_object* v_snd_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5423_; 
v_a_5302_ = lean_ctor_get(v___x_5301_, 0);
lean_inc(v_a_5302_);
lean_dec_ref_known(v___x_5301_, 1);
v_fst_5303_ = lean_ctor_get(v_a_5302_, 0);
v_snd_5304_ = lean_ctor_get(v_a_5302_, 1);
v_isSharedCheck_5423_ = !lean_is_exclusive(v_a_5302_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5306_ = v_a_5302_;
v_isShared_5307_ = v_isSharedCheck_5423_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_snd_5304_);
lean_inc(v_fst_5303_);
lean_dec(v_a_5302_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5423_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5308_; 
v___x_5308_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5281_, v_a_4704_, v_snd_5304_);
if (lean_obj_tag(v___x_5308_) == 0)
{
lean_object* v_a_5309_; lean_object* v_fst_5310_; lean_object* v_snd_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5414_; 
v_a_5309_ = lean_ctor_get(v___x_5308_, 0);
lean_inc(v_a_5309_);
lean_dec_ref_known(v___x_5308_, 1);
v_fst_5310_ = lean_ctor_get(v_a_5309_, 0);
v_snd_5311_ = lean_ctor_get(v_a_5309_, 1);
v_isSharedCheck_5414_ = !lean_is_exclusive(v_a_5309_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5313_ = v_a_5309_;
v_isShared_5314_ = v_isSharedCheck_5414_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_snd_5311_);
lean_inc(v_fst_5310_);
lean_dec(v_a_5309_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5414_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5315_; 
v___x_5315_ = l_LeanExport_dumpExpr(v_type_5282_, v_a_4704_, v_snd_5311_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v_a_5316_; lean_object* v_fst_5317_; lean_object* v_snd_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5405_; 
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
lean_inc(v_a_5316_);
lean_dec_ref_known(v___x_5315_, 1);
v_fst_5317_ = lean_ctor_get(v_a_5316_, 0);
v_snd_5318_ = lean_ctor_get(v_a_5316_, 1);
v_isSharedCheck_5405_ = !lean_is_exclusive(v_a_5316_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5320_ = v_a_5316_;
v_isShared_5321_ = v_isSharedCheck_5405_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_snd_5318_);
lean_inc(v_fst_5317_);
lean_dec(v_a_5316_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5405_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5322_; 
v___x_5322_ = l_LeanExport_dumpExpr(v_value_5277_, v_a_4704_, v_snd_5318_);
if (lean_obj_tag(v___x_5322_) == 0)
{
lean_object* v_a_5323_; lean_object* v_fst_5324_; lean_object* v_snd_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5396_; 
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
lean_inc(v_a_5323_);
lean_dec_ref_known(v___x_5322_, 1);
v_fst_5324_ = lean_ctor_get(v_a_5323_, 0);
v_snd_5325_ = lean_ctor_get(v_a_5323_, 1);
v_isSharedCheck_5396_ = !lean_is_exclusive(v_a_5323_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5327_ = v_a_5323_;
v_isShared_5328_ = v_isSharedCheck_5396_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_snd_5325_);
lean_inc(v_fst_5324_);
lean_dec(v_a_5323_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5396_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5329_; 
v___x_5329_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5279_, v_a_4704_, v_snd_5325_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_object* v_a_5330_; lean_object* v_fst_5331_; lean_object* v_snd_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5387_; 
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
lean_inc(v_a_5330_);
lean_dec_ref_known(v___x_5329_, 1);
v_fst_5331_ = lean_ctor_get(v_a_5330_, 0);
v_snd_5332_ = lean_ctor_get(v_a_5330_, 1);
v_isSharedCheck_5387_ = !lean_is_exclusive(v_a_5330_);
if (v_isSharedCheck_5387_ == 0)
{
v___x_5334_ = v_a_5330_;
v_isShared_5335_ = v_isSharedCheck_5387_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_snd_5332_);
lean_inc(v_fst_5331_);
lean_dec(v_a_5330_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5387_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5340_; 
v___x_5336_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0));
v___x_5337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_5338_ = l_Lean_JsonNumber_fromNat(v_fst_5303_);
if (v_isShared_5296_ == 0)
{
lean_ctor_set_tag(v___x_5295_, 2);
lean_ctor_set(v___x_5295_, 0, v___x_5338_);
v___x_5340_ = v___x_5295_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5386_; 
v_reuseFailAlloc_5386_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5386_, 0, v___x_5338_);
v___x_5340_ = v_reuseFailAlloc_5386_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
lean_object* v___x_5342_; 
if (v_isShared_5335_ == 0)
{
lean_ctor_set(v___x_5334_, 1, v___x_5340_);
lean_ctor_set(v___x_5334_, 0, v___x_5337_);
v___x_5342_ = v___x_5334_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v___x_5337_);
lean_ctor_set(v_reuseFailAlloc_5385_, 1, v___x_5340_);
v___x_5342_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
lean_object* v___x_5343_; lean_object* v___x_5345_; 
v___x_5343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 1, v_fst_5310_);
lean_ctor_set(v___x_5327_, 0, v___x_5343_);
v___x_5345_ = v___x_5327_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v___x_5343_);
lean_ctor_set(v_reuseFailAlloc_5384_, 1, v_fst_5310_);
v___x_5345_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5349_; 
v___x_5346_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5347_ = l_Lean_JsonNumber_fromNat(v_fst_5317_);
if (v_isShared_5287_ == 0)
{
lean_ctor_set_tag(v___x_5286_, 2);
lean_ctor_set(v___x_5286_, 0, v___x_5347_);
v___x_5349_ = v___x_5286_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5347_);
v___x_5349_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
lean_object* v___x_5351_; 
if (v_isShared_5321_ == 0)
{
lean_ctor_set(v___x_5320_, 1, v___x_5349_);
lean_ctor_set(v___x_5320_, 0, v___x_5346_);
v___x_5351_ = v___x_5320_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v___x_5346_);
lean_ctor_set(v_reuseFailAlloc_5382_, 1, v___x_5349_);
v___x_5351_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5355_; 
v___x_5352_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5353_ = l_Lean_JsonNumber_fromNat(v_fst_5324_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set_tag(v___x_5274_, 2);
lean_ctor_set(v___x_5274_, 0, v___x_5353_);
v___x_5355_ = v___x_5274_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v___x_5353_);
v___x_5355_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
lean_object* v___x_5357_; 
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 1, v___x_5355_);
lean_ctor_set(v___x_5313_, 0, v___x_5352_);
v___x_5357_ = v___x_5313_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5352_);
lean_ctor_set(v_reuseFailAlloc_5380_, 1, v___x_5355_);
v___x_5357_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
lean_object* v___x_5358_; lean_object* v___x_5360_; 
v___x_5358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 1, v_fst_5331_);
lean_ctor_set(v___x_5306_, 0, v___x_5358_);
v___x_5360_ = v___x_5306_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v___x_5358_);
lean_ctor_set(v_reuseFailAlloc_5379_, 1, v_fst_5331_);
v___x_5360_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5364_; 
v___x_5361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6));
v___x_5362_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5362_, 0, v_isUnsafe_5278_);
if (v_isShared_5300_ == 0)
{
lean_ctor_set(v___x_5299_, 1, v___x_5362_);
lean_ctor_set(v___x_5299_, 0, v___x_5361_);
v___x_5364_ = v___x_5299_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5378_; 
v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5361_);
lean_ctor_set(v_reuseFailAlloc_5378_, 1, v___x_5362_);
v___x_5364_ = v_reuseFailAlloc_5378_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5374_; 
v___x_5365_ = lean_box(0);
v___x_5366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5366_, 0, v___x_5364_);
lean_ctor_set(v___x_5366_, 1, v___x_5365_);
v___x_5367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5367_, 0, v___x_5360_);
lean_ctor_set(v___x_5367_, 1, v___x_5366_);
v___x_5368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5357_);
lean_ctor_set(v___x_5368_, 1, v___x_5367_);
v___x_5369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5369_, 0, v___x_5351_);
lean_ctor_set(v___x_5369_, 1, v___x_5368_);
v___x_5370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5370_, 0, v___x_5345_);
lean_ctor_set(v___x_5370_, 1, v___x_5369_);
v___x_5371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5371_, 0, v___x_5342_);
lean_ctor_set(v___x_5371_, 1, v___x_5370_);
v___x_5372_ = l_Lean_Json_mkObj(v___x_5371_);
lean_dec_ref_known(v___x_5371_, 2);
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 1, v___x_5372_);
lean_ctor_set(v___x_5290_, 0, v___x_5336_);
v___x_5374_ = v___x_5290_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v___x_5336_);
lean_ctor_set(v_reuseFailAlloc_5377_, 1, v___x_5372_);
v___x_5374_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
lean_object* v___x_5375_; lean_object* v___x_5376_; 
v___x_5375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5374_);
lean_ctor_set(v___x_5375_, 1, v___x_5365_);
v___x_5376_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5375_, v_snd_5332_);
lean_dec_ref_known(v___x_5375_, 2);
return v___x_5376_;
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
lean_object* v_a_5388_; lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5395_; 
lean_del_object(v___x_5327_);
lean_dec(v_fst_5324_);
lean_del_object(v___x_5320_);
lean_dec(v_fst_5317_);
lean_del_object(v___x_5313_);
lean_dec(v_fst_5310_);
lean_del_object(v___x_5306_);
lean_dec(v_fst_5303_);
lean_del_object(v___x_5299_);
lean_del_object(v___x_5295_);
lean_del_object(v___x_5290_);
lean_del_object(v___x_5286_);
lean_del_object(v___x_5274_);
v_a_5388_ = lean_ctor_get(v___x_5329_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5390_ = v___x_5329_;
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
else
{
lean_inc(v_a_5388_);
lean_dec(v___x_5329_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v___x_5393_; 
if (v_isShared_5391_ == 0)
{
v___x_5393_ = v___x_5390_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_a_5388_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
}
}
}
else
{
lean_object* v_a_5397_; lean_object* v___x_5399_; uint8_t v_isShared_5400_; uint8_t v_isSharedCheck_5404_; 
lean_del_object(v___x_5320_);
lean_dec(v_fst_5317_);
lean_del_object(v___x_5313_);
lean_dec(v_fst_5310_);
lean_del_object(v___x_5306_);
lean_dec(v_fst_5303_);
lean_del_object(v___x_5299_);
lean_del_object(v___x_5295_);
lean_del_object(v___x_5290_);
lean_del_object(v___x_5286_);
lean_dec(v_all_5279_);
lean_del_object(v___x_5274_);
v_a_5397_ = lean_ctor_get(v___x_5322_, 0);
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5322_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5399_ = v___x_5322_;
v_isShared_5400_ = v_isSharedCheck_5404_;
goto v_resetjp_5398_;
}
else
{
lean_inc(v_a_5397_);
lean_dec(v___x_5322_);
v___x_5399_ = lean_box(0);
v_isShared_5400_ = v_isSharedCheck_5404_;
goto v_resetjp_5398_;
}
v_resetjp_5398_:
{
lean_object* v___x_5402_; 
if (v_isShared_5400_ == 0)
{
v___x_5402_ = v___x_5399_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_a_5397_);
v___x_5402_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
return v___x_5402_;
}
}
}
}
}
else
{
lean_object* v_a_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5413_; 
lean_del_object(v___x_5313_);
lean_dec(v_fst_5310_);
lean_del_object(v___x_5306_);
lean_dec(v_fst_5303_);
lean_del_object(v___x_5299_);
lean_del_object(v___x_5295_);
lean_del_object(v___x_5290_);
lean_del_object(v___x_5286_);
lean_dec(v_all_5279_);
lean_dec_ref(v_value_5277_);
lean_del_object(v___x_5274_);
v_a_5406_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5413_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5408_ = v___x_5315_;
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_a_5406_);
lean_dec(v___x_5315_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v___x_5411_; 
if (v_isShared_5409_ == 0)
{
v___x_5411_ = v___x_5408_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_a_5406_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
return v___x_5411_;
}
}
}
}
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
lean_del_object(v___x_5306_);
lean_dec(v_fst_5303_);
lean_del_object(v___x_5299_);
lean_del_object(v___x_5295_);
lean_del_object(v___x_5290_);
lean_del_object(v___x_5286_);
lean_dec_ref(v_type_5282_);
lean_dec(v_all_5279_);
lean_dec_ref(v_value_5277_);
lean_del_object(v___x_5274_);
v_a_5415_ = lean_ctor_get(v___x_5308_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5308_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5417_ = v___x_5308_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5308_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_a_5415_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_del_object(v___x_5299_);
lean_del_object(v___x_5295_);
lean_del_object(v___x_5290_);
lean_del_object(v___x_5286_);
lean_dec_ref(v_type_5282_);
lean_dec(v_levelParams_5281_);
lean_dec(v_all_5279_);
lean_dec_ref(v_value_5277_);
lean_del_object(v___x_5274_);
v_a_5424_ = lean_ctor_get(v___x_5301_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5301_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5301_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5290_);
lean_del_object(v___x_5286_);
lean_dec_ref(v_type_5282_);
lean_dec(v_levelParams_5281_);
lean_dec(v_name_5280_);
lean_dec(v_all_5279_);
lean_dec_ref(v_value_5277_);
lean_del_object(v___x_5274_);
return v___x_5292_;
}
}
}
}
else
{
lean_dec_ref(v_type_5282_);
lean_dec(v_levelParams_5281_);
lean_dec(v_name_5280_);
lean_dec(v_all_5279_);
lean_dec_ref(v_value_5277_);
lean_del_object(v___x_5274_);
return v___x_5283_;
}
}
}
case 4:
{
lean_object* v___x_5439_; lean_object* v___x_5440_; 
lean_dec_ref_known(v_val_4815_, 1);
v___x_5439_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__9));
v___x_5440_ = l_LeanExport_dumpConstant(v___x_5439_, v_a_4704_, v___x_4832_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v_a_5441_; lean_object* v_snd_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
v_a_5441_ = lean_ctor_get(v___x_5440_, 0);
lean_inc(v_a_5441_);
lean_dec_ref_known(v___x_5440_, 1);
v_snd_5442_ = lean_ctor_get(v_a_5441_, 1);
lean_inc(v_snd_5442_);
lean_dec(v_a_5441_);
v___x_5443_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__19));
v___x_5444_ = lean_box(0);
v___x_5445_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
v___x_5446_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_4826_, v___x_5443_, v___x_5445_, v_a_4704_, v_snd_5442_);
if (lean_obj_tag(v___x_5446_) == 0)
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5473_; 
v_a_5447_ = lean_ctor_get(v___x_5446_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5446_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5449_ = v___x_5446_;
v_isShared_5450_ = v_isSharedCheck_5473_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5446_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5473_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v_fst_5451_; lean_object* v_fst_5452_; lean_object* v___x_5454_; uint8_t v_isShared_5455_; uint8_t v_isSharedCheck_5471_; 
v_fst_5451_ = lean_ctor_get(v_a_5447_, 0);
lean_inc(v_fst_5451_);
v_fst_5452_ = lean_ctor_get(v_fst_5451_, 0);
v_isSharedCheck_5471_ = !lean_is_exclusive(v_fst_5451_);
if (v_isSharedCheck_5471_ == 0)
{
lean_object* v_unused_5472_; 
v_unused_5472_ = lean_ctor_get(v_fst_5451_, 1);
lean_dec(v_unused_5472_);
v___x_5454_ = v_fst_5451_;
v_isShared_5455_ = v_isSharedCheck_5471_;
goto v_resetjp_5453_;
}
else
{
lean_inc(v_fst_5452_);
lean_dec(v_fst_5451_);
v___x_5454_ = lean_box(0);
v_isShared_5455_ = v_isSharedCheck_5471_;
goto v_resetjp_5453_;
}
v_resetjp_5453_:
{
if (lean_obj_tag(v_fst_5452_) == 0)
{
lean_object* v_snd_5456_; lean_object* v___x_5458_; 
v_snd_5456_ = lean_ctor_get(v_a_5447_, 1);
lean_inc(v_snd_5456_);
lean_dec(v_a_5447_);
if (v_isShared_5455_ == 0)
{
lean_ctor_set(v___x_5454_, 1, v_snd_5456_);
lean_ctor_set(v___x_5454_, 0, v___x_5444_);
v___x_5458_ = v___x_5454_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v___x_5444_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v_snd_5456_);
v___x_5458_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
lean_object* v___x_5460_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 0, v___x_5458_);
v___x_5460_ = v___x_5449_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v___x_5458_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
else
{
lean_object* v_snd_5463_; lean_object* v_val_5464_; lean_object* v___x_5466_; 
v_snd_5463_ = lean_ctor_get(v_a_5447_, 1);
lean_inc(v_snd_5463_);
lean_dec(v_a_5447_);
v_val_5464_ = lean_ctor_get(v_fst_5452_, 0);
lean_inc(v_val_5464_);
lean_dec_ref_known(v_fst_5452_, 1);
if (v_isShared_5455_ == 0)
{
lean_ctor_set(v___x_5454_, 1, v_snd_5463_);
lean_ctor_set(v___x_5454_, 0, v_val_5464_);
v___x_5466_ = v___x_5454_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_val_5464_);
lean_ctor_set(v_reuseFailAlloc_5470_, 1, v_snd_5463_);
v___x_5466_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
lean_object* v___x_5468_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 0, v___x_5466_);
v___x_5468_ = v___x_5449_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v___x_5466_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
}
}
else
{
lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5481_; 
v_a_5474_ = lean_ctor_get(v___x_5446_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5446_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5476_ = v___x_5446_;
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5446_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5479_; 
if (v_isShared_5477_ == 0)
{
v___x_5479_ = v___x_5476_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5474_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
else
{
return v___x_5440_;
}
}
case 5:
{
lean_object* v_val_5482_; lean_object* v_all_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; 
v_val_5482_ = lean_ctor_get(v_val_4815_, 0);
lean_inc_ref(v_val_5482_);
lean_dec_ref_known(v_val_4815_, 1);
v_all_5483_ = lean_ctor_get(v_val_5482_, 3);
lean_inc(v_all_5483_);
v___x_5484_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_5485_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__22, &l_LeanExport_dumpConstant___closed__22_once, _init_l_LeanExport_dumpConstant___closed__22);
v___x_5486_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_4826_, v_val_5482_, v_all_5483_, v___x_5485_, v_a_4704_, v___x_4832_);
lean_dec(v_all_5483_);
lean_dec_ref(v_val_5482_);
if (lean_obj_tag(v___x_5486_) == 0)
{
lean_object* v_a_5487_; lean_object* v_fst_5488_; lean_object* v_snd_5489_; lean_object* v_snd_5490_; lean_object* v_fst_5491_; lean_object* v_fst_5492_; lean_object* v_snd_5493_; lean_object* v___x_5494_; size_t v_sz_5495_; size_t v___x_5496_; lean_object* v___x_5497_; 
v_a_5487_ = lean_ctor_get(v___x_5486_, 0);
lean_inc(v_a_5487_);
lean_dec_ref_known(v___x_5486_, 1);
v_fst_5488_ = lean_ctor_get(v_a_5487_, 0);
lean_inc(v_fst_5488_);
v_snd_5489_ = lean_ctor_get(v_fst_5488_, 1);
lean_inc(v_snd_5489_);
v_snd_5490_ = lean_ctor_get(v_a_5487_, 1);
lean_inc(v_snd_5490_);
lean_dec(v_a_5487_);
v_fst_5491_ = lean_ctor_get(v_fst_5488_, 0);
lean_inc(v_fst_5491_);
lean_dec(v_fst_5488_);
v_fst_5492_ = lean_ctor_get(v_snd_5489_, 0);
lean_inc(v_fst_5492_);
v_snd_5493_ = lean_ctor_get(v_snd_5489_, 1);
lean_inc(v_snd_5493_);
lean_dec(v_snd_5489_);
v___x_5494_ = lean_box(0);
v_sz_5495_ = lean_array_size(v_fst_5492_);
v___x_5496_ = ((size_t)0ULL);
v___x_5497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_fst_5492_, v_sz_5495_, v___x_5496_, v___x_5494_, v_a_4704_, v_snd_5490_);
if (lean_obj_tag(v___x_5497_) == 0)
{
lean_object* v_a_5498_; lean_object* v_snd_5499_; lean_object* v___x_5500_; 
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc(v_a_5498_);
lean_dec_ref_known(v___x_5497_, 1);
v_snd_5499_ = lean_ctor_get(v_a_5498_, 1);
lean_inc(v_snd_5499_);
lean_dec(v_a_5498_);
v___x_5500_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15(v___x_4826_, v___x_5484_, v_snd_5493_, v_a_4704_, v_snd_5499_);
if (lean_obj_tag(v___x_5500_) == 0)
{
lean_object* v_a_5501_; lean_object* v_fst_5502_; lean_object* v_snd_5503_; lean_object* v_a_5504_; 
v_a_5501_ = lean_ctor_get(v___x_5500_, 0);
lean_inc(v_a_5501_);
lean_dec_ref_known(v___x_5500_, 1);
v_fst_5502_ = lean_ctor_get(v_a_5501_, 0);
lean_inc(v_fst_5502_);
v_snd_5503_ = lean_ctor_get(v_a_5501_, 1);
lean_inc(v_snd_5503_);
lean_dec(v_a_5501_);
v_a_5504_ = lean_ctor_get(v_fst_5502_, 0);
lean_inc(v_a_5504_);
lean_dec(v_fst_5502_);
v___y_4712_ = v_fst_5491_;
v___y_4713_ = v___x_5494_;
v___y_4714_ = v_sz_5495_;
v___y_4715_ = v_fst_5492_;
v___y_4716_ = v___x_5496_;
v_fst_4717_ = v_a_5504_;
v_snd_4718_ = v_snd_5503_;
goto v___jp_4711_;
}
else
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5512_; 
lean_dec(v_fst_5492_);
lean_dec(v_fst_5491_);
v_a_5505_ = lean_ctor_get(v___x_5500_, 0);
v_isSharedCheck_5512_ = !lean_is_exclusive(v___x_5500_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5507_ = v___x_5500_;
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5500_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5510_; 
if (v_isShared_5508_ == 0)
{
v___x_5510_ = v___x_5507_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_a_5505_);
v___x_5510_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
return v___x_5510_;
}
}
}
}
else
{
lean_dec(v_snd_5493_);
lean_dec(v_fst_5492_);
lean_dec(v_fst_5491_);
return v___x_5497_;
}
}
else
{
lean_object* v_a_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5520_; 
v_a_5513_ = lean_ctor_get(v___x_5486_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5515_ = v___x_5486_;
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_a_5513_);
lean_dec(v___x_5486_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5518_; 
if (v_isShared_5516_ == 0)
{
v___x_5518_ = v___x_5515_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5513_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
}
case 6:
{
lean_object* v_val_5521_; lean_object* v_induct_5522_; 
v_val_5521_ = lean_ctor_get(v_val_4815_, 0);
lean_inc_ref(v_val_5521_);
lean_dec_ref_known(v_val_4815_, 1);
v_induct_5522_ = lean_ctor_get(v_val_5521_, 1);
lean_inc(v_induct_5522_);
lean_dec_ref(v_val_5521_);
v_c_4703_ = v_induct_5522_;
v_a_4705_ = v___x_4832_;
goto _start;
}
default: 
{
lean_object* v_val_5524_; lean_object* v_all_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; 
v_val_5524_ = lean_ctor_get(v_val_4815_, 0);
lean_inc_ref(v_val_5524_);
lean_dec_ref_known(v_val_4815_, 1);
v_all_5525_ = lean_ctor_get(v_val_5524_, 1);
lean_inc(v_all_5525_);
lean_dec_ref(v_val_5524_);
v___x_5526_ = lean_box(0);
v___x_5527_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_all_5525_, v___x_5526_, v_a_4704_, v___x_4832_);
lean_dec(v_all_5525_);
if (lean_obj_tag(v___x_5527_) == 0)
{
lean_object* v_a_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5544_; 
v_a_5528_ = lean_ctor_get(v___x_5527_, 0);
v_isSharedCheck_5544_ = !lean_is_exclusive(v___x_5527_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5530_ = v___x_5527_;
v_isShared_5531_ = v_isSharedCheck_5544_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_a_5528_);
lean_dec(v___x_5527_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5544_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v_snd_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5542_; 
v_snd_5532_ = lean_ctor_get(v_a_5528_, 1);
v_isSharedCheck_5542_ = !lean_is_exclusive(v_a_5528_);
if (v_isSharedCheck_5542_ == 0)
{
lean_object* v_unused_5543_; 
v_unused_5543_ = lean_ctor_get(v_a_5528_, 0);
lean_dec(v_unused_5543_);
v___x_5534_ = v_a_5528_;
v_isShared_5535_ = v_isSharedCheck_5542_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_snd_5532_);
lean_dec(v_a_5528_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5542_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
lean_ctor_set(v___x_5534_, 0, v___x_5526_);
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v___x_5526_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v_snd_5532_);
v___x_5537_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
lean_object* v___x_5539_; 
if (v_isShared_5531_ == 0)
{
lean_ctor_set(v___x_5530_, 0, v___x_5537_);
v___x_5539_ = v___x_5530_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v___x_5537_);
v___x_5539_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
return v___x_5539_;
}
}
}
}
}
else
{
return v___x_5527_;
}
}
}
}
}
}
else
{
lean_dec(v_val_4815_);
lean_dec(v_c_4703_);
goto v___jp_4707_;
}
}
v___jp_5553_:
{
if (v___y_5554_ == 0)
{
goto v___jp_4816_;
}
else
{
lean_dec(v_val_4815_);
lean_dec(v_c_4703_);
goto v___jp_4707_;
}
}
}
else
{
uint8_t v_ignoreMissing_5557_; 
lean_dec(v___x_4814_);
v_ignoreMissing_5557_ = lean_ctor_get_uint8(v_a_4705_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_5557_ == 0)
{
lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; uint8_t v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; 
v___x_5558_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_5559_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_5560_ = lean_unsigned_to_nat(254u);
v___x_5561_ = lean_unsigned_to_nat(48u);
v___x_5562_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_5563_ = 1;
v___x_5564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_4703_, v___x_5563_);
v___x_5565_ = lean_string_append(v___x_5562_, v___x_5564_);
lean_dec_ref(v___x_5564_);
v___x_5566_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_5567_ = lean_string_append(v___x_5565_, v___x_5566_);
v___x_5568_ = l_mkPanicMessageWithDecl(v___x_5558_, v___x_5559_, v___x_5560_, v___x_5561_, v___x_5567_);
lean_dec_ref(v___x_5567_);
v___x_5569_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_5568_, v_a_4704_, v_a_4705_);
return v___x_5569_;
}
else
{
lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; 
lean_dec(v_c_4703_);
v___x_5570_ = lean_box(0);
v___x_5571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5571_, 0, v___x_5570_);
lean_ctor_set(v___x_5571_, 1, v_a_4705_);
v___x_5572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5572_, 0, v___x_5571_);
return v___x_5572_;
}
}
v___jp_4707_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = lean_box(0);
v___x_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
lean_ctor_set(v___x_4709_, 1, v_a_4705_);
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
return v___x_4710_;
}
v___jp_4711_:
{
size_t v_sz_4719_; lean_object* v___x_4720_; 
v_sz_4719_ = lean_array_size(v_fst_4717_);
v___x_4720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16(v_fst_4717_, v_sz_4719_, v___y_4716_, v___y_4713_, v_a_4704_, v_snd_4718_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v_snd_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4811_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4720_, 1);
v_snd_4722_ = lean_ctor_get(v_a_4721_, 1);
v_isSharedCheck_4811_ = !lean_is_exclusive(v_a_4721_);
if (v_isSharedCheck_4811_ == 0)
{
lean_object* v_unused_4812_; 
v_unused_4812_ = lean_ctor_get(v_a_4721_, 0);
lean_dec(v_unused_4812_);
v___x_4724_ = v_a_4721_;
v_isShared_4725_ = v_isSharedCheck_4811_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_snd_4722_);
lean_dec(v_a_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4811_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4726_; 
v___x_4726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17(v_fst_4717_, v_sz_4719_, v___y_4716_, v___y_4713_, v_a_4704_, v_snd_4722_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; lean_object* v_snd_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4809_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_a_4727_);
lean_dec_ref_known(v___x_4726_, 1);
v_snd_4728_ = lean_ctor_get(v_a_4727_, 1);
v_isSharedCheck_4809_ = !lean_is_exclusive(v_a_4727_);
if (v_isSharedCheck_4809_ == 0)
{
lean_object* v_unused_4810_; 
v_unused_4810_ = lean_ctor_get(v_a_4727_, 0);
lean_dec(v_unused_4810_);
v___x_4730_ = v_a_4727_;
v_isShared_4731_ = v_isSharedCheck_4809_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_snd_4728_);
lean_dec(v_a_4727_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4809_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
size_t v_sz_4732_; lean_object* v___x_4733_; 
v_sz_4732_ = lean_array_size(v___y_4712_);
v___x_4733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_4732_, v___y_4716_, v___y_4712_, v_a_4704_, v_snd_4728_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; lean_object* v_fst_4735_; lean_object* v_snd_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4800_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4733_, 1);
v_fst_4735_ = lean_ctor_get(v_a_4734_, 0);
v_snd_4736_ = lean_ctor_get(v_a_4734_, 1);
v_isSharedCheck_4800_ = !lean_is_exclusive(v_a_4734_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4738_ = v_a_4734_;
v_isShared_4739_ = v_isSharedCheck_4800_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_snd_4736_);
lean_inc(v_fst_4735_);
lean_dec(v_a_4734_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4800_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4740_; 
v___x_4740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19(v___y_4714_, v___y_4716_, v___y_4715_, v_a_4704_, v_snd_4736_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; lean_object* v_fst_4742_; lean_object* v_snd_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4791_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref_known(v___x_4740_, 1);
v_fst_4742_ = lean_ctor_get(v_a_4741_, 0);
v_snd_4743_ = lean_ctor_get(v_a_4741_, 1);
v_isSharedCheck_4791_ = !lean_is_exclusive(v_a_4741_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4745_ = v_a_4741_;
v_isShared_4746_ = v_isSharedCheck_4791_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_snd_4743_);
lean_inc(v_fst_4742_);
lean_dec(v_a_4741_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4791_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4747_; 
v___x_4747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20(v_sz_4719_, v___y_4716_, v_fst_4717_, v_a_4704_, v_snd_4743_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; lean_object* v_fst_4749_; lean_object* v_snd_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4782_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref_known(v___x_4747_, 1);
v_fst_4749_ = lean_ctor_get(v_a_4748_, 0);
v_snd_4750_ = lean_ctor_get(v_a_4748_, 1);
v_isSharedCheck_4782_ = !lean_is_exclusive(v_a_4748_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4752_ = v_a_4748_;
v_isShared_4753_ = v_isSharedCheck_4782_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_snd_4750_);
lean_inc(v_fst_4749_);
lean_dec(v_a_4748_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4782_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4758_; 
v___x_4754_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__0));
v___x_4755_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__1));
v___x_4756_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(v_fst_4735_);
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 1, v___x_4756_);
lean_ctor_set(v___x_4752_, 0, v___x_4755_);
v___x_4758_ = v___x_4752_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4755_);
lean_ctor_set(v_reuseFailAlloc_4781_, 1, v___x_4756_);
v___x_4758_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4762_; 
v___x_4759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2));
v___x_4760_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(v_fst_4742_);
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 1, v___x_4760_);
lean_ctor_set(v___x_4745_, 0, v___x_4759_);
v___x_4762_ = v___x_4745_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4759_);
lean_ctor_set(v_reuseFailAlloc_4780_, 1, v___x_4760_);
v___x_4762_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4766_; 
v___x_4763_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__2));
v___x_4764_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(v_fst_4749_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 1, v___x_4764_);
lean_ctor_set(v___x_4738_, 0, v___x_4763_);
v___x_4766_ = v___x_4738_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4763_);
lean_ctor_set(v_reuseFailAlloc_4779_, 1, v___x_4764_);
v___x_4766_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
lean_object* v___x_4767_; lean_object* v___x_4769_; 
v___x_4767_ = lean_box(0);
if (v_isShared_4725_ == 0)
{
lean_ctor_set_tag(v___x_4724_, 1);
lean_ctor_set(v___x_4724_, 1, v___x_4767_);
lean_ctor_set(v___x_4724_, 0, v___x_4766_);
v___x_4769_ = v___x_4724_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4766_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v___x_4767_);
v___x_4769_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4774_; 
v___x_4770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4770_, 0, v___x_4762_);
lean_ctor_set(v___x_4770_, 1, v___x_4769_);
v___x_4771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4758_);
lean_ctor_set(v___x_4771_, 1, v___x_4770_);
v___x_4772_ = l_Lean_Json_mkObj(v___x_4771_);
lean_dec_ref_known(v___x_4771_, 2);
if (v_isShared_4731_ == 0)
{
lean_ctor_set(v___x_4730_, 1, v___x_4772_);
lean_ctor_set(v___x_4730_, 0, v___x_4754_);
v___x_4774_ = v___x_4730_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4754_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v___x_4772_);
v___x_4774_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4774_);
lean_ctor_set(v___x_4775_, 1, v___x_4767_);
v___x_4776_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4775_, v_snd_4750_);
lean_dec_ref_known(v___x_4775_, 2);
return v___x_4776_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
lean_del_object(v___x_4745_);
lean_dec(v_fst_4742_);
lean_del_object(v___x_4738_);
lean_dec(v_fst_4735_);
lean_del_object(v___x_4730_);
lean_del_object(v___x_4724_);
v_a_4783_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4747_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4747_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_del_object(v___x_4738_);
lean_dec(v_fst_4735_);
lean_del_object(v___x_4730_);
lean_del_object(v___x_4724_);
lean_dec_ref(v_fst_4717_);
v_a_4792_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4740_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4740_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
lean_del_object(v___x_4730_);
lean_del_object(v___x_4724_);
lean_dec_ref(v_fst_4717_);
lean_dec(v___y_4715_);
v_a_4801_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4733_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4733_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
}
else
{
lean_del_object(v___x_4724_);
lean_dec_ref(v_fst_4717_);
lean_dec(v___y_4715_);
lean_dec(v___y_4712_);
return v___x_4726_;
}
}
}
else
{
lean_dec_ref(v_fst_4717_);
lean_dec(v___y_4715_);
lean_dec(v___y_4712_);
return v___x_4720_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(lean_object* v_as_5573_, size_t v_sz_5574_, size_t v_i_5575_, lean_object* v_b_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_){
_start:
{
uint8_t v___x_5580_; 
v___x_5580_ = lean_usize_dec_lt(v_i_5575_, v_sz_5574_);
if (v___x_5580_ == 0)
{
lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5581_, 0, v_b_5576_);
lean_ctor_set(v___x_5581_, 1, v___y_5578_);
v___x_5582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
return v___x_5582_;
}
else
{
lean_object* v_a_5583_; lean_object* v___x_5584_; 
v_a_5583_ = lean_array_uget_borrowed(v_as_5573_, v_i_5575_);
lean_inc(v_a_5583_);
v___x_5584_ = l_LeanExport_dumpConstant(v_a_5583_, v___y_5577_, v___y_5578_);
if (lean_obj_tag(v___x_5584_) == 0)
{
lean_object* v_a_5585_; lean_object* v_snd_5586_; lean_object* v___x_5587_; size_t v___x_5588_; size_t v___x_5589_; 
v_a_5585_ = lean_ctor_get(v___x_5584_, 0);
lean_inc(v_a_5585_);
lean_dec_ref_known(v___x_5584_, 1);
v_snd_5586_ = lean_ctor_get(v_a_5585_, 1);
lean_inc(v_snd_5586_);
lean_dec(v_a_5585_);
v___x_5587_ = lean_box(0);
v___x_5588_ = ((size_t)1ULL);
v___x_5589_ = lean_usize_add(v_i_5575_, v___x_5588_);
v_i_5575_ = v___x_5589_;
v_b_5576_ = v___x_5587_;
v___y_5578_ = v_snd_5586_;
goto _start;
}
else
{
return v___x_5584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(lean_object* v_e_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_){
_start:
{
lean_object* v___x_5595_; lean_object* v___x_5596_; size_t v_sz_5597_; size_t v___x_5598_; lean_object* v___x_5599_; 
v___x_5595_ = l_Lean_Expr_getUsedConstants(v_e_5591_);
v___x_5596_ = lean_box(0);
v_sz_5597_ = lean_array_size(v___x_5595_);
v___x_5598_ = ((size_t)0ULL);
v___x_5599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v___x_5595_, v_sz_5597_, v___x_5598_, v___x_5596_, v_a_5592_, v_a_5593_);
lean_dec_ref(v___x_5595_);
if (lean_obj_tag(v___x_5599_) == 0)
{
lean_object* v_a_5600_; lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5616_; 
v_a_5600_ = lean_ctor_get(v___x_5599_, 0);
v_isSharedCheck_5616_ = !lean_is_exclusive(v___x_5599_);
if (v_isSharedCheck_5616_ == 0)
{
v___x_5602_ = v___x_5599_;
v_isShared_5603_ = v_isSharedCheck_5616_;
goto v_resetjp_5601_;
}
else
{
lean_inc(v_a_5600_);
lean_dec(v___x_5599_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5616_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v_snd_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5614_; 
v_snd_5604_ = lean_ctor_get(v_a_5600_, 1);
v_isSharedCheck_5614_ = !lean_is_exclusive(v_a_5600_);
if (v_isSharedCheck_5614_ == 0)
{
lean_object* v_unused_5615_; 
v_unused_5615_ = lean_ctor_get(v_a_5600_, 0);
lean_dec(v_unused_5615_);
v___x_5606_ = v_a_5600_;
v_isShared_5607_ = v_isSharedCheck_5614_;
goto v_resetjp_5605_;
}
else
{
lean_inc(v_snd_5604_);
lean_dec(v_a_5600_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5614_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v___x_5609_; 
if (v_isShared_5607_ == 0)
{
lean_ctor_set(v___x_5606_, 0, v___x_5596_);
v___x_5609_ = v___x_5606_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5596_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v_snd_5604_);
v___x_5609_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
lean_object* v___x_5611_; 
if (v_isShared_5603_ == 0)
{
lean_ctor_set(v___x_5602_, 0, v___x_5609_);
v___x_5611_ = v___x_5602_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v___x_5609_);
v___x_5611_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
return v___x_5611_;
}
}
}
}
}
else
{
return v___x_5599_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps___boxed(lean_object* v_e_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_){
_start:
{
lean_object* v_res_5621_; 
v_res_5621_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_e_5617_, v_a_5618_, v_a_5619_);
lean_dec_ref(v_a_5618_);
return v_res_5621_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg___boxed(lean_object* v_as_x27_5622_, lean_object* v_b_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_){
_start:
{
lean_object* v_res_5627_; 
v_res_5627_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5622_, v_b_5623_, v___y_5624_, v___y_5625_);
lean_dec_ref(v___y_5624_);
lean_dec(v_as_x27_5622_);
return v_res_5627_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg___boxed(lean_object* v_as_x27_5628_, lean_object* v_b_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_){
_start:
{
lean_object* v_res_5633_; 
v_res_5633_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5628_, v_b_5629_, v___y_5630_, v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v_as_x27_5628_);
return v_res_5633_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2___boxed(lean_object* v_x_5634_, lean_object* v_x_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_x_5634_, v_x_5635_, v___y_5636_, v___y_5637_);
lean_dec_ref(v___y_5636_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0___boxed(lean_object* v_as_5640_, lean_object* v_sz_5641_, lean_object* v_i_5642_, lean_object* v_b_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_){
_start:
{
size_t v_sz_boxed_5647_; size_t v_i_boxed_5648_; lean_object* v_res_5649_; 
v_sz_boxed_5647_ = lean_unbox_usize(v_sz_5641_);
lean_dec(v_sz_5641_);
v_i_boxed_5648_ = lean_unbox_usize(v_i_5642_);
lean_dec(v_i_5642_);
v_res_5649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v_as_5640_, v_sz_boxed_5647_, v_i_boxed_5648_, v_b_5643_, v___y_5644_, v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec_ref(v_as_5640_);
return v_res_5649_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___boxed(lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_){
_start:
{
lean_object* v_res_5653_; 
v_res_5653_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_5650_, v_a_5651_);
lean_dec_ref(v_a_5650_);
return v_res_5653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object* v_as_5654_, lean_object* v_sz_5655_, lean_object* v_i_5656_, lean_object* v_b_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_){
_start:
{
size_t v_sz_boxed_5661_; size_t v_i_boxed_5662_; lean_object* v_res_5663_; 
v_sz_boxed_5661_ = lean_unbox_usize(v_sz_5655_);
lean_dec(v_sz_5655_);
v_i_boxed_5662_ = lean_unbox_usize(v_i_5656_);
lean_dec(v_i_5656_);
v_res_5663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17(v_as_5654_, v_sz_boxed_5661_, v_i_boxed_5662_, v_b_5657_, v___y_5658_, v___y_5659_);
lean_dec_ref(v___y_5658_);
lean_dec_ref(v_as_5654_);
return v_res_5663_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object* v_e_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_){
_start:
{
lean_object* v_res_5668_; 
v_res_5668_ = l_LeanExport_dumpExpr(v_e_5664_, v_a_5665_, v_a_5666_);
lean_dec_ref(v_a_5665_);
return v_res_5668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object* v_as_5669_, lean_object* v_sz_5670_, lean_object* v_i_5671_, lean_object* v_b_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_){
_start:
{
size_t v_sz_boxed_5676_; size_t v_i_boxed_5677_; lean_object* v_res_5678_; 
v_sz_boxed_5676_ = lean_unbox_usize(v_sz_5670_);
lean_dec(v_sz_5670_);
v_i_boxed_5677_ = lean_unbox_usize(v_i_5671_);
lean_dec(v_i_5671_);
v_res_5678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_as_5669_, v_sz_boxed_5676_, v_i_boxed_5677_, v_b_5672_, v___y_5673_, v___y_5674_);
lean_dec_ref(v___y_5673_);
lean_dec_ref(v_as_5669_);
return v_res_5678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object* v_as_5679_, lean_object* v_sz_5680_, lean_object* v_i_5681_, lean_object* v_b_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_){
_start:
{
size_t v_sz_boxed_5686_; size_t v_i_boxed_5687_; lean_object* v_res_5688_; 
v_sz_boxed_5686_ = lean_unbox_usize(v_sz_5680_);
lean_dec(v_sz_5680_);
v_i_boxed_5687_ = lean_unbox_usize(v_i_5681_);
lean_dec(v_i_5681_);
v_res_5688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16(v_as_5679_, v_sz_boxed_5686_, v_i_boxed_5687_, v_b_5682_, v___y_5683_, v___y_5684_);
lean_dec_ref(v___y_5683_);
lean_dec_ref(v_as_5679_);
return v_res_5688_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object* v_rule_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_){
_start:
{
lean_object* v_res_5693_; 
v_res_5693_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_rule_5689_, v_a_5690_, v_a_5691_);
lean_dec_ref(v_a_5690_);
return v_res_5693_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_){
_start:
{
lean_object* v_res_5697_; 
v_res_5697_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_5694_, v_a_5695_);
lean_dec_ref(v_a_5694_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___boxed(lean_object* v_sz_5698_, lean_object* v_i_5699_, lean_object* v_bs_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_){
_start:
{
size_t v_sz_boxed_5704_; size_t v_i_boxed_5705_; lean_object* v_res_5706_; 
v_sz_boxed_5704_ = lean_unbox_usize(v_sz_5698_);
lean_dec(v_sz_5698_);
v_i_boxed_5705_ = lean_unbox_usize(v_i_5699_);
lean_dec(v_i_5699_);
v_res_5706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19(v_sz_boxed_5704_, v_i_boxed_5705_, v_bs_5700_, v___y_5701_, v___y_5702_);
lean_dec_ref(v___y_5701_);
return v_res_5706_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object* v___x_5707_, lean_object* v_as_x27_5708_, lean_object* v_b_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_){
_start:
{
uint8_t v___x_173051__boxed_5713_; lean_object* v_res_5714_; 
v___x_173051__boxed_5713_ = lean_unbox(v___x_5707_);
v_res_5714_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_173051__boxed_5713_, v_as_x27_5708_, v_b_5709_, v___y_5710_, v___y_5711_);
lean_dec_ref(v___y_5710_);
lean_dec(v_as_x27_5708_);
return v_res_5714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object* v_sz_5715_, lean_object* v_i_5716_, lean_object* v_bs_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_){
_start:
{
size_t v_sz_boxed_5721_; size_t v_i_boxed_5722_; lean_object* v_res_5723_; 
v_sz_boxed_5721_ = lean_unbox_usize(v_sz_5715_);
lean_dec(v_sz_5715_);
v_i_boxed_5722_ = lean_unbox_usize(v_i_5716_);
lean_dec(v_i_5716_);
v_res_5723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_boxed_5721_, v_i_boxed_5722_, v_bs_5717_, v___y_5718_, v___y_5719_);
lean_dec_ref(v___y_5718_);
return v_res_5723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object* v_sz_5724_, lean_object* v_i_5725_, lean_object* v_bs_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_){
_start:
{
size_t v_sz_boxed_5730_; size_t v_i_boxed_5731_; lean_object* v_res_5732_; 
v_sz_boxed_5730_ = lean_unbox_usize(v_sz_5724_);
lean_dec(v_sz_5724_);
v_i_boxed_5731_ = lean_unbox_usize(v_i_5725_);
lean_dec(v_i_5725_);
v_res_5732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20(v_sz_boxed_5730_, v_i_boxed_5731_, v_bs_5726_, v___y_5727_, v___y_5728_);
lean_dec_ref(v___y_5727_);
return v_res_5732_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___boxed(lean_object* v___x_5733_, lean_object* v_val_5734_, lean_object* v_as_x27_5735_, lean_object* v_b_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_){
_start:
{
uint8_t v___x_173356__boxed_5740_; lean_object* v_res_5741_; 
v___x_173356__boxed_5740_ = lean_unbox(v___x_5733_);
v_res_5741_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_173356__boxed_5740_, v_val_5734_, v_as_x27_5735_, v_b_5736_, v___y_5737_, v___y_5738_);
lean_dec_ref(v___y_5737_);
lean_dec(v_as_x27_5735_);
lean_dec_ref(v_val_5734_);
return v_res_5741_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux___boxed(lean_object* v_e_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_){
_start:
{
lean_object* v_res_5746_; 
v_res_5746_ = l_LeanExport_dumpExprAux(v_e_5742_, v_a_5743_, v_a_5744_);
lean_dec_ref(v_a_5743_);
return v_res_5746_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant___boxed(lean_object* v_c_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_){
_start:
{
lean_object* v_res_5751_; 
v_res_5751_ = l_LeanExport_dumpConstant(v_c_5747_, v_a_5748_, v_a_5749_);
lean_dec_ref(v_a_5748_);
return v_res_5751_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(uint8_t v___x_5752_, lean_object* v_as_5753_, lean_object* v_as_x27_5754_, lean_object* v_b_5755_, lean_object* v_a_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_){
_start:
{
lean_object* v___x_5760_; 
v___x_5760_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_5752_, v_as_x27_5754_, v_b_5755_, v___y_5757_, v___y_5758_);
return v___x_5760_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___boxed(lean_object* v___x_5761_, lean_object* v_as_5762_, lean_object* v_as_x27_5763_, lean_object* v_b_5764_, lean_object* v_a_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_){
_start:
{
uint8_t v___x_177923__boxed_5769_; lean_object* v_res_5770_; 
v___x_177923__boxed_5769_ = lean_unbox(v___x_5761_);
v_res_5770_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(v___x_177923__boxed_5769_, v_as_5762_, v_as_x27_5763_, v_b_5764_, v_a_5765_, v___y_5766_, v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v_as_x27_5763_);
lean_dec(v_as_5762_);
return v_res_5770_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(uint8_t v___y_5771_, uint8_t v___x_5772_, lean_object* v_as_5773_, lean_object* v_as_x27_5774_, lean_object* v_b_5775_, lean_object* v_a_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_){
_start:
{
lean_object* v___x_5780_; 
v___x_5780_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_5771_, v___x_5772_, v_as_x27_5774_, v_b_5775_, v___y_5777_, v___y_5778_);
return v___x_5780_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___boxed(lean_object* v___y_5781_, lean_object* v___x_5782_, lean_object* v_as_5783_, lean_object* v_as_x27_5784_, lean_object* v_b_5785_, lean_object* v_a_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_){
_start:
{
uint8_t v___y_177940__boxed_5790_; uint8_t v___x_177941__boxed_5791_; lean_object* v_res_5792_; 
v___y_177940__boxed_5790_ = lean_unbox(v___y_5781_);
v___x_177941__boxed_5791_ = lean_unbox(v___x_5782_);
v_res_5792_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(v___y_177940__boxed_5790_, v___x_177941__boxed_5791_, v_as_5783_, v_as_x27_5784_, v_b_5785_, v_a_5786_, v___y_5787_, v___y_5788_);
lean_dec_ref(v___y_5787_);
lean_dec(v_as_x27_5784_);
lean_dec(v_as_5783_);
return v_res_5792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(lean_object* v_00_u03b4_5793_, lean_object* v_t_5794_, lean_object* v_k_5795_){
_start:
{
lean_object* v___x_5796_; 
v___x_5796_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_5794_, v_k_5795_);
return v___x_5796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___boxed(lean_object* v_00_u03b4_5797_, lean_object* v_t_5798_, lean_object* v_k_5799_){
_start:
{
lean_object* v_res_5800_; 
v_res_5800_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(v_00_u03b4_5797_, v_t_5798_, v_k_5799_);
lean_dec(v_k_5799_);
lean_dec(v_t_5798_);
return v_res_5800_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(uint8_t v___x_5801_, lean_object* v_val_5802_, lean_object* v_as_5803_, lean_object* v_as_x27_5804_, lean_object* v_b_5805_, lean_object* v_a_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_){
_start:
{
lean_object* v___x_5810_; 
v___x_5810_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_5801_, v_val_5802_, v_as_x27_5804_, v_b_5805_, v___y_5807_, v___y_5808_);
return v___x_5810_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___boxed(lean_object* v___x_5811_, lean_object* v_val_5812_, lean_object* v_as_5813_, lean_object* v_as_x27_5814_, lean_object* v_b_5815_, lean_object* v_a_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_){
_start:
{
uint8_t v___x_177962__boxed_5820_; lean_object* v_res_5821_; 
v___x_177962__boxed_5820_ = lean_unbox(v___x_5811_);
v_res_5821_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(v___x_177962__boxed_5820_, v_val_5812_, v_as_5813_, v_as_x27_5814_, v_b_5815_, v_a_5816_, v___y_5817_, v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v_as_x27_5814_);
lean_dec(v_as_5813_);
lean_dec_ref(v_val_5812_);
return v_res_5821_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(lean_object* v_as_5822_, lean_object* v_as_x27_5823_, lean_object* v_b_5824_, lean_object* v_a_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_){
_start:
{
lean_object* v___x_5829_; 
v___x_5829_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5823_, v_b_5824_, v___y_5826_, v___y_5827_);
return v___x_5829_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___boxed(lean_object* v_as_5830_, lean_object* v_as_x27_5831_, lean_object* v_b_5832_, lean_object* v_a_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_){
_start:
{
lean_object* v_res_5837_; 
v_res_5837_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(v_as_5830_, v_as_x27_5831_, v_b_5832_, v_a_5833_, v___y_5834_, v___y_5835_);
lean_dec_ref(v___y_5834_);
lean_dec(v_as_x27_5831_);
lean_dec(v_as_5830_);
return v_res_5837_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(lean_object* v_as_5838_, lean_object* v_as_x27_5839_, lean_object* v_b_5840_, lean_object* v_a_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_){
_start:
{
lean_object* v___x_5845_; 
v___x_5845_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5839_, v_b_5840_, v___y_5842_, v___y_5843_);
return v___x_5845_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___boxed(lean_object* v_as_5846_, lean_object* v_as_x27_5847_, lean_object* v_b_5848_, lean_object* v_a_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_){
_start:
{
lean_object* v_res_5853_; 
v_res_5853_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(v_as_5846_, v_as_x27_5847_, v_b_5848_, v_a_5849_, v___y_5850_, v___y_5851_);
lean_dec_ref(v___y_5850_);
lean_dec(v_as_x27_5847_);
lean_dec(v_as_5846_);
return v_res_5853_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1(void){
_start:
{
lean_object* v___x_5855_; lean_object* v___x_5856_; 
v___x_5855_ = l_Lean_versionString;
v___x_5856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5855_);
return v___x_5856_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; 
v___x_5857_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1);
v___x_5858_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0));
v___x_5859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5859_, 0, v___x_5858_);
lean_ctor_set(v___x_5859_, 1, v___x_5857_);
return v___x_5859_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4(void){
_start:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5861_ = l_Lean_githash;
v___x_5862_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5862_, 0, v___x_5861_);
return v___x_5862_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5(void){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; 
v___x_5863_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4);
v___x_5864_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3));
v___x_5865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5864_);
lean_ctor_set(v___x_5865_, 1, v___x_5863_);
return v___x_5865_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6(void){
_start:
{
lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5866_ = lean_box(0);
v___x_5867_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5);
v___x_5868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5867_);
lean_ctor_set(v___x_5868_, 1, v___x_5866_);
return v___x_5868_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7(void){
_start:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; 
v___x_5869_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6);
v___x_5870_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2);
v___x_5871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5871_, 0, v___x_5870_);
lean_ctor_set(v___x_5871_, 1, v___x_5869_);
return v___x_5871_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8(void){
_start:
{
lean_object* v___x_5872_; lean_object* v_leanMeta_5873_; 
v___x_5872_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7);
v_leanMeta_5873_ = l_Lean_Json_mkObj(v___x_5872_);
return v_leanMeta_5873_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17(void){
_start:
{
lean_object* v___x_5892_; lean_object* v_exporterMeta_5893_; 
v___x_5892_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16));
v_exporterMeta_5893_ = l_Lean_Json_mkObj(v___x_5892_);
return v_exporterMeta_5893_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18(void){
_start:
{
lean_object* v___x_5894_; lean_object* v_formatMeta_5895_; 
v___x_5894_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15));
v_formatMeta_5895_ = l_Lean_Json_mkObj(v___x_5894_);
return v_formatMeta_5895_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21(void){
_start:
{
lean_object* v_exporterMeta_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; 
v_exporterMeta_5898_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17);
v___x_5899_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20));
v___x_5900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5899_);
lean_ctor_set(v___x_5900_, 1, v_exporterMeta_5898_);
return v___x_5900_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23(void){
_start:
{
lean_object* v_leanMeta_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; 
v_leanMeta_5902_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8);
v___x_5903_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22));
v___x_5904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5904_, 0, v___x_5903_);
lean_ctor_set(v___x_5904_, 1, v_leanMeta_5902_);
return v___x_5904_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25(void){
_start:
{
lean_object* v_formatMeta_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v_formatMeta_5906_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18);
v___x_5907_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24));
v___x_5908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5907_);
lean_ctor_set(v___x_5908_, 1, v_formatMeta_5906_);
return v___x_5908_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26(void){
_start:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; 
v___x_5909_ = lean_box(0);
v___x_5910_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25);
v___x_5911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5910_);
lean_ctor_set(v___x_5911_, 1, v___x_5909_);
return v___x_5911_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27(void){
_start:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___x_5912_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26);
v___x_5913_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23);
v___x_5914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5913_);
lean_ctor_set(v___x_5914_, 1, v___x_5912_);
return v___x_5914_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28(void){
_start:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v___x_5915_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27);
v___x_5916_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21);
v___x_5917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5916_);
lean_ctor_set(v___x_5917_, 1, v___x_5915_);
return v___x_5917_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29(void){
_start:
{
lean_object* v___x_5918_; lean_object* v___x_5919_; 
v___x_5918_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28);
v___x_5919_ = l_Lean_Json_mkObj(v___x_5918_);
return v___x_5919_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30(void){
_start:
{
lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5920_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29);
v___x_5921_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19));
v___x_5922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5922_, 0, v___x_5921_);
lean_ctor_set(v___x_5922_, 1, v___x_5920_);
return v___x_5922_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31(void){
_start:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; 
v___x_5923_ = lean_box(0);
v___x_5924_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30);
v___x_5925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5925_, 0, v___x_5924_);
lean_ctor_set(v___x_5925_, 1, v___x_5923_);
return v___x_5925_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32(void){
_start:
{
lean_object* v___x_5926_; lean_object* v___x_5927_; 
v___x_5926_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31);
v___x_5927_ = l_Lean_Json_mkObj(v___x_5926_);
return v___x_5927_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata(void){
_start:
{
lean_object* v___x_5928_; 
v___x_5928_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32);
return v___x_5928_;
}
}
static lean_object* _init_l_LeanExport_dumpMetadata___redArg___closed__0(void){
_start:
{
lean_object* v___x_5929_; lean_object* v___x_5930_; 
v___x_5929_ = l___private_LeanExport_Basic_0__LeanExport_exportMetadata;
v___x_5930_ = l_Lean_Json_compress(v___x_5929_);
return v___x_5930_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg(lean_object* v_a_5931_){
_start:
{
lean_object* v___x_5933_; lean_object* v___x_5934_; 
v___x_5933_ = lean_obj_once(&l_LeanExport_dumpMetadata___redArg___closed__0, &l_LeanExport_dumpMetadata___redArg___closed__0_once, _init_l_LeanExport_dumpMetadata___redArg___closed__0);
v___x_5934_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_5933_);
if (lean_obj_tag(v___x_5934_) == 0)
{
lean_object* v_a_5935_; lean_object* v___x_5937_; uint8_t v_isShared_5938_; uint8_t v_isSharedCheck_5943_; 
v_a_5935_ = lean_ctor_get(v___x_5934_, 0);
v_isSharedCheck_5943_ = !lean_is_exclusive(v___x_5934_);
if (v_isSharedCheck_5943_ == 0)
{
v___x_5937_ = v___x_5934_;
v_isShared_5938_ = v_isSharedCheck_5943_;
goto v_resetjp_5936_;
}
else
{
lean_inc(v_a_5935_);
lean_dec(v___x_5934_);
v___x_5937_ = lean_box(0);
v_isShared_5938_ = v_isSharedCheck_5943_;
goto v_resetjp_5936_;
}
v_resetjp_5936_:
{
lean_object* v___x_5939_; lean_object* v___x_5941_; 
v___x_5939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5939_, 0, v_a_5935_);
lean_ctor_set(v___x_5939_, 1, v_a_5931_);
if (v_isShared_5938_ == 0)
{
lean_ctor_set(v___x_5937_, 0, v___x_5939_);
v___x_5941_ = v___x_5937_;
goto v_reusejp_5940_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v___x_5939_);
v___x_5941_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5940_;
}
v_reusejp_5940_:
{
return v___x_5941_;
}
}
}
else
{
lean_object* v_a_5944_; lean_object* v___x_5946_; uint8_t v_isShared_5947_; uint8_t v_isSharedCheck_5951_; 
lean_dec_ref(v_a_5931_);
v_a_5944_ = lean_ctor_get(v___x_5934_, 0);
v_isSharedCheck_5951_ = !lean_is_exclusive(v___x_5934_);
if (v_isSharedCheck_5951_ == 0)
{
v___x_5946_ = v___x_5934_;
v_isShared_5947_ = v_isSharedCheck_5951_;
goto v_resetjp_5945_;
}
else
{
lean_inc(v_a_5944_);
lean_dec(v___x_5934_);
v___x_5946_ = lean_box(0);
v_isShared_5947_ = v_isSharedCheck_5951_;
goto v_resetjp_5945_;
}
v_resetjp_5945_:
{
lean_object* v___x_5949_; 
if (v_isShared_5947_ == 0)
{
v___x_5949_ = v___x_5946_;
goto v_reusejp_5948_;
}
else
{
lean_object* v_reuseFailAlloc_5950_; 
v_reuseFailAlloc_5950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5950_, 0, v_a_5944_);
v___x_5949_ = v_reuseFailAlloc_5950_;
goto v_reusejp_5948_;
}
v_reusejp_5948_:
{
return v___x_5949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg___boxed(lean_object* v_a_5952_, lean_object* v_a_5953_){
_start:
{
lean_object* v_res_5954_; 
v_res_5954_ = l_LeanExport_dumpMetadata___redArg(v_a_5952_);
return v_res_5954_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata(lean_object* v_a_5955_, lean_object* v_a_5956_){
_start:
{
lean_object* v___x_5958_; 
v___x_5958_ = l_LeanExport_dumpMetadata___redArg(v_a_5956_);
return v___x_5958_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___boxed(lean_object* v_a_5959_, lean_object* v_a_5960_, lean_object* v_a_5961_){
_start:
{
lean_object* v_res_5962_; 
v_res_5962_ = l_LeanExport_dumpMetadata(v_a_5959_, v_a_5960_);
lean_dec_ref(v_a_5959_);
return v_res_5962_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(lean_object* v_as_x27_5963_, lean_object* v_b_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_){
_start:
{
if (lean_obj_tag(v_as_x27_5963_) == 0)
{
lean_object* v___x_5968_; lean_object* v___x_5969_; 
v___x_5968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5968_, 0, v_b_5964_);
lean_ctor_set(v___x_5968_, 1, v___y_5966_);
v___x_5969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
return v___x_5969_;
}
else
{
lean_object* v_head_5970_; lean_object* v_tail_5971_; lean_object* v_visitedNames_5972_; lean_object* v_visitedLevels_5973_; lean_object* v_visitedExprs_5974_; lean_object* v_visitedConstants_5975_; uint8_t v_exportMData_5976_; uint8_t v_exportUnsafe_5977_; uint8_t v_ignoreMissing_5978_; lean_object* v_recursorMap_5979_; lean_object* v___x_5981_; uint8_t v_isShared_5982_; uint8_t v_isSharedCheck_5992_; 
v_head_5970_ = lean_ctor_get(v_as_x27_5963_, 0);
v_tail_5971_ = lean_ctor_get(v_as_x27_5963_, 1);
v_visitedNames_5972_ = lean_ctor_get(v___y_5966_, 0);
v_visitedLevels_5973_ = lean_ctor_get(v___y_5966_, 1);
v_visitedExprs_5974_ = lean_ctor_get(v___y_5966_, 2);
v_visitedConstants_5975_ = lean_ctor_get(v___y_5966_, 3);
v_exportMData_5976_ = lean_ctor_get_uint8(v___y_5966_, sizeof(void*)*6);
v_exportUnsafe_5977_ = lean_ctor_get_uint8(v___y_5966_, sizeof(void*)*6 + 1);
v_ignoreMissing_5978_ = lean_ctor_get_uint8(v___y_5966_, sizeof(void*)*6 + 2);
v_recursorMap_5979_ = lean_ctor_get(v___y_5966_, 5);
v_isSharedCheck_5992_ = !lean_is_exclusive(v___y_5966_);
if (v_isSharedCheck_5992_ == 0)
{
lean_object* v_unused_5993_; 
v_unused_5993_ = lean_ctor_get(v___y_5966_, 4);
lean_dec(v_unused_5993_);
v___x_5981_ = v___y_5966_;
v_isShared_5982_ = v_isSharedCheck_5992_;
goto v_resetjp_5980_;
}
else
{
lean_inc(v_recursorMap_5979_);
lean_inc(v_visitedConstants_5975_);
lean_inc(v_visitedExprs_5974_);
lean_inc(v_visitedLevels_5973_);
lean_inc(v_visitedNames_5972_);
lean_dec(v___y_5966_);
v___x_5981_ = lean_box(0);
v_isShared_5982_ = v_isSharedCheck_5992_;
goto v_resetjp_5980_;
}
v_resetjp_5980_:
{
lean_object* v___x_5983_; lean_object* v___x_5985_; 
v___x_5983_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_5982_ == 0)
{
lean_ctor_set(v___x_5981_, 4, v___x_5983_);
v___x_5985_ = v___x_5981_;
goto v_reusejp_5984_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v_visitedNames_5972_);
lean_ctor_set(v_reuseFailAlloc_5991_, 1, v_visitedLevels_5973_);
lean_ctor_set(v_reuseFailAlloc_5991_, 2, v_visitedExprs_5974_);
lean_ctor_set(v_reuseFailAlloc_5991_, 3, v_visitedConstants_5975_);
lean_ctor_set(v_reuseFailAlloc_5991_, 4, v___x_5983_);
lean_ctor_set(v_reuseFailAlloc_5991_, 5, v_recursorMap_5979_);
lean_ctor_set_uint8(v_reuseFailAlloc_5991_, sizeof(void*)*6, v_exportMData_5976_);
lean_ctor_set_uint8(v_reuseFailAlloc_5991_, sizeof(void*)*6 + 1, v_exportUnsafe_5977_);
lean_ctor_set_uint8(v_reuseFailAlloc_5991_, sizeof(void*)*6 + 2, v_ignoreMissing_5978_);
v___x_5985_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5984_;
}
v_reusejp_5984_:
{
lean_object* v___x_5986_; 
lean_inc(v_head_5970_);
v___x_5986_ = l_LeanExport_dumpConstant(v_head_5970_, v___y_5965_, v___x_5985_);
if (lean_obj_tag(v___x_5986_) == 0)
{
lean_object* v_a_5987_; lean_object* v_snd_5988_; lean_object* v___x_5989_; 
v_a_5987_ = lean_ctor_get(v___x_5986_, 0);
lean_inc(v_a_5987_);
lean_dec_ref_known(v___x_5986_, 1);
v_snd_5988_ = lean_ctor_get(v_a_5987_, 1);
lean_inc(v_snd_5988_);
lean_dec(v_a_5987_);
v___x_5989_ = lean_box(0);
v_as_x27_5963_ = v_tail_5971_;
v_b_5964_ = v___x_5989_;
v___y_5966_ = v_snd_5988_;
goto _start;
}
else
{
return v___x_5986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg___boxed(lean_object* v_as_x27_5994_, lean_object* v_b_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_){
_start:
{
lean_object* v_res_5999_; 
v_res_5999_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_5994_, v_b_5995_, v___y_5996_, v___y_5997_);
lean_dec_ref(v___y_5996_);
lean_dec(v_as_x27_5994_);
return v_res_5999_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0(lean_object* v_env_6000_, lean_object* v_cliOptions_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_){
_start:
{
lean_object* v___x_6006_; 
v___x_6006_ = l_LeanExport_initState(v_env_6000_, v_cliOptions_6001_, v___y_6003_, v___y_6004_);
if (lean_obj_tag(v___x_6006_) == 0)
{
lean_object* v_a_6007_; lean_object* v_snd_6008_; lean_object* v___x_6009_; 
v_a_6007_ = lean_ctor_get(v___x_6006_, 0);
lean_inc(v_a_6007_);
lean_dec_ref_known(v___x_6006_, 1);
v_snd_6008_ = lean_ctor_get(v_a_6007_, 1);
lean_inc(v_snd_6008_);
lean_dec(v_a_6007_);
v___x_6009_ = l_LeanExport_dumpMetadata___redArg(v_snd_6008_);
if (lean_obj_tag(v___x_6009_) == 0)
{
lean_object* v_a_6010_; lean_object* v_snd_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; 
v_a_6010_ = lean_ctor_get(v___x_6009_, 0);
lean_inc(v_a_6010_);
lean_dec_ref_known(v___x_6009_, 1);
v_snd_6011_ = lean_ctor_get(v_a_6010_, 1);
lean_inc(v_snd_6011_);
lean_dec(v_a_6010_);
v___x_6012_ = lean_box(0);
v___x_6013_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v___y_6002_, v___x_6012_, v___y_6003_, v_snd_6011_);
if (lean_obj_tag(v___x_6013_) == 0)
{
lean_object* v_a_6014_; lean_object* v___x_6016_; uint8_t v_isShared_6017_; uint8_t v_isSharedCheck_6030_; 
v_a_6014_ = lean_ctor_get(v___x_6013_, 0);
v_isSharedCheck_6030_ = !lean_is_exclusive(v___x_6013_);
if (v_isSharedCheck_6030_ == 0)
{
v___x_6016_ = v___x_6013_;
v_isShared_6017_ = v_isSharedCheck_6030_;
goto v_resetjp_6015_;
}
else
{
lean_inc(v_a_6014_);
lean_dec(v___x_6013_);
v___x_6016_ = lean_box(0);
v_isShared_6017_ = v_isSharedCheck_6030_;
goto v_resetjp_6015_;
}
v_resetjp_6015_:
{
lean_object* v_snd_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6028_; 
v_snd_6018_ = lean_ctor_get(v_a_6014_, 1);
v_isSharedCheck_6028_ = !lean_is_exclusive(v_a_6014_);
if (v_isSharedCheck_6028_ == 0)
{
lean_object* v_unused_6029_; 
v_unused_6029_ = lean_ctor_get(v_a_6014_, 0);
lean_dec(v_unused_6029_);
v___x_6020_ = v_a_6014_;
v_isShared_6021_ = v_isSharedCheck_6028_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_snd_6018_);
lean_dec(v_a_6014_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6028_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
lean_object* v___x_6023_; 
if (v_isShared_6021_ == 0)
{
lean_ctor_set(v___x_6020_, 0, v___x_6012_);
v___x_6023_ = v___x_6020_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6027_; 
v_reuseFailAlloc_6027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6027_, 0, v___x_6012_);
lean_ctor_set(v_reuseFailAlloc_6027_, 1, v_snd_6018_);
v___x_6023_ = v_reuseFailAlloc_6027_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
lean_object* v___x_6025_; 
if (v_isShared_6017_ == 0)
{
lean_ctor_set(v___x_6016_, 0, v___x_6023_);
v___x_6025_ = v___x_6016_;
goto v_reusejp_6024_;
}
else
{
lean_object* v_reuseFailAlloc_6026_; 
v_reuseFailAlloc_6026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6026_, 0, v___x_6023_);
v___x_6025_ = v_reuseFailAlloc_6026_;
goto v_reusejp_6024_;
}
v_reusejp_6024_:
{
return v___x_6025_;
}
}
}
}
}
else
{
return v___x_6013_;
}
}
else
{
return v___x_6009_;
}
}
else
{
return v___x_6006_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0___boxed(lean_object* v_env_6031_, lean_object* v_cliOptions_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_){
_start:
{
lean_object* v_res_6037_; 
v_res_6037_ = l_LeanExport_dumpEnv___lam__0(v_env_6031_, v_cliOptions_6032_, v___y_6033_, v___y_6034_, v___y_6035_);
lean_dec_ref(v___y_6034_);
lean_dec(v___y_6033_);
lean_dec(v_cliOptions_6032_);
return v_res_6037_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___lam__0(lean_object* v_es_6038_, lean_object* v_a_6039_, lean_object* v_b_6040_){
_start:
{
lean_object* v___x_6041_; lean_object* v___x_6042_; 
v___x_6041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6041_, 0, v_a_6039_);
lean_ctor_set(v___x_6041_, 1, v_b_6040_);
v___x_6042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6041_);
lean_ctor_set(v___x_6042_, 1, v_es_6038_);
return v___x_6042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(lean_object* v_f_6043_, lean_object* v_x_6044_, lean_object* v_x_6045_){
_start:
{
if (lean_obj_tag(v_x_6045_) == 0)
{
lean_dec(v_f_6043_);
return v_x_6044_;
}
else
{
lean_object* v_key_6046_; lean_object* v_value_6047_; lean_object* v_tail_6048_; lean_object* v___x_6049_; 
v_key_6046_ = lean_ctor_get(v_x_6045_, 0);
lean_inc(v_key_6046_);
v_value_6047_ = lean_ctor_get(v_x_6045_, 1);
lean_inc(v_value_6047_);
v_tail_6048_ = lean_ctor_get(v_x_6045_, 2);
lean_inc(v_tail_6048_);
lean_dec_ref_known(v_x_6045_, 3);
lean_inc(v_f_6043_);
v___x_6049_ = lean_apply_3(v_f_6043_, v_x_6044_, v_key_6046_, v_value_6047_);
v_x_6044_ = v___x_6049_;
v_x_6045_ = v_tail_6048_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(lean_object* v_f_6051_, lean_object* v_as_6052_, size_t v_i_6053_, size_t v_stop_6054_, lean_object* v_b_6055_){
_start:
{
uint8_t v___x_6056_; 
v___x_6056_ = lean_usize_dec_eq(v_i_6053_, v_stop_6054_);
if (v___x_6056_ == 0)
{
lean_object* v___x_6057_; lean_object* v___x_6058_; size_t v___x_6059_; size_t v___x_6060_; 
v___x_6057_ = lean_array_uget_borrowed(v_as_6052_, v_i_6053_);
lean_inc(v___x_6057_);
lean_inc(v_f_6051_);
v___x_6058_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(v_f_6051_, v_b_6055_, v___x_6057_);
v___x_6059_ = ((size_t)1ULL);
v___x_6060_ = lean_usize_add(v_i_6053_, v___x_6059_);
v_i_6053_ = v___x_6060_;
v_b_6055_ = v___x_6058_;
goto _start;
}
else
{
lean_dec(v_f_6051_);
return v_b_6055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_f_6062_, lean_object* v_as_6063_, lean_object* v_i_6064_, lean_object* v_stop_6065_, lean_object* v_b_6066_){
_start:
{
size_t v_i_boxed_6067_; size_t v_stop_boxed_6068_; lean_object* v_res_6069_; 
v_i_boxed_6067_ = lean_unbox_usize(v_i_6064_);
lean_dec(v_i_6064_);
v_stop_boxed_6068_ = lean_unbox_usize(v_stop_6065_);
lean_dec(v_stop_6065_);
v_res_6069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6062_, v_as_6063_, v_i_boxed_6067_, v_stop_boxed_6068_, v_b_6066_);
lean_dec_ref(v_as_6063_);
return v_res_6069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0(lean_object* v_f_6070_, lean_object* v_x1_6071_, lean_object* v_x2_6072_, lean_object* v_x3_6073_){
_start:
{
lean_object* v___x_6074_; 
v___x_6074_ = lean_apply_3(v_f_6070_, v_x1_6071_, v_x2_6072_, v_x3_6073_);
return v___x_6074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(lean_object* v_f_6075_, lean_object* v_keys_6076_, lean_object* v_vals_6077_, lean_object* v_i_6078_, lean_object* v_acc_6079_){
_start:
{
lean_object* v___x_6080_; uint8_t v___x_6081_; 
v___x_6080_ = lean_array_get_size(v_keys_6076_);
v___x_6081_ = lean_nat_dec_lt(v_i_6078_, v___x_6080_);
if (v___x_6081_ == 0)
{
lean_dec(v_i_6078_);
lean_dec(v_f_6075_);
return v_acc_6079_;
}
else
{
lean_object* v_k_6082_; lean_object* v_v_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; 
v_k_6082_ = lean_array_fget_borrowed(v_keys_6076_, v_i_6078_);
v_v_6083_ = lean_array_fget_borrowed(v_vals_6077_, v_i_6078_);
lean_inc(v_f_6075_);
lean_inc(v_v_6083_);
lean_inc(v_k_6082_);
v___x_6084_ = lean_apply_3(v_f_6075_, v_acc_6079_, v_k_6082_, v_v_6083_);
v___x_6085_ = lean_unsigned_to_nat(1u);
v___x_6086_ = lean_nat_add(v_i_6078_, v___x_6085_);
lean_dec(v_i_6078_);
v_i_6078_ = v___x_6086_;
v_acc_6079_ = v___x_6084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg___boxed(lean_object* v_f_6088_, lean_object* v_keys_6089_, lean_object* v_vals_6090_, lean_object* v_i_6091_, lean_object* v_acc_6092_){
_start:
{
lean_object* v_res_6093_; 
v_res_6093_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6088_, v_keys_6089_, v_vals_6090_, v_i_6091_, v_acc_6092_);
lean_dec_ref(v_vals_6090_);
lean_dec_ref(v_keys_6089_);
return v_res_6093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(lean_object* v_f_6094_, lean_object* v_as_6095_, size_t v_i_6096_, size_t v_stop_6097_, lean_object* v_b_6098_){
_start:
{
lean_object* v___y_6100_; uint8_t v___x_6104_; 
v___x_6104_ = lean_usize_dec_eq(v_i_6096_, v_stop_6097_);
if (v___x_6104_ == 0)
{
lean_object* v___x_6105_; 
v___x_6105_ = lean_array_uget_borrowed(v_as_6095_, v_i_6096_);
switch(lean_obj_tag(v___x_6105_))
{
case 0:
{
lean_object* v_key_6106_; lean_object* v_val_6107_; lean_object* v___x_6108_; 
v_key_6106_ = lean_ctor_get(v___x_6105_, 0);
v_val_6107_ = lean_ctor_get(v___x_6105_, 1);
lean_inc(v_f_6094_);
lean_inc(v_val_6107_);
lean_inc(v_key_6106_);
v___x_6108_ = lean_apply_3(v_f_6094_, v_b_6098_, v_key_6106_, v_val_6107_);
v___y_6100_ = v___x_6108_;
goto v___jp_6099_;
}
case 1:
{
lean_object* v_node_6109_; lean_object* v___x_6110_; 
v_node_6109_ = lean_ctor_get(v___x_6105_, 0);
lean_inc(v_f_6094_);
v___x_6110_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6094_, v_node_6109_, v_b_6098_);
v___y_6100_ = v___x_6110_;
goto v___jp_6099_;
}
default: 
{
v___y_6100_ = v_b_6098_;
goto v___jp_6099_;
}
}
}
else
{
lean_dec(v_f_6094_);
return v_b_6098_;
}
v___jp_6099_:
{
size_t v___x_6101_; size_t v___x_6102_; 
v___x_6101_ = ((size_t)1ULL);
v___x_6102_ = lean_usize_add(v_i_6096_, v___x_6101_);
v_i_6096_ = v___x_6102_;
v_b_6098_ = v___y_6100_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_f_6111_, lean_object* v_x_6112_, lean_object* v_x_6113_){
_start:
{
if (lean_obj_tag(v_x_6112_) == 0)
{
lean_object* v_es_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; uint8_t v___x_6117_; 
v_es_6114_ = lean_ctor_get(v_x_6112_, 0);
v___x_6115_ = lean_unsigned_to_nat(0u);
v___x_6116_ = lean_array_get_size(v_es_6114_);
v___x_6117_ = lean_nat_dec_lt(v___x_6115_, v___x_6116_);
if (v___x_6117_ == 0)
{
lean_dec(v_f_6111_);
return v_x_6113_;
}
else
{
size_t v___x_6118_; size_t v___x_6119_; lean_object* v___x_6120_; 
v___x_6118_ = ((size_t)0ULL);
v___x_6119_ = lean_usize_of_nat(v___x_6116_);
v___x_6120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6111_, v_es_6114_, v___x_6118_, v___x_6119_, v_x_6113_);
return v___x_6120_;
}
}
else
{
lean_object* v_ks_6121_; lean_object* v_vs_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; 
v_ks_6121_ = lean_ctor_get(v_x_6112_, 0);
v_vs_6122_ = lean_ctor_get(v_x_6112_, 1);
v___x_6123_ = lean_unsigned_to_nat(0u);
v___x_6124_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6111_, v_ks_6121_, v_vs_6122_, v___x_6123_, v_x_6113_);
return v___x_6124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v_f_6125_, lean_object* v_x_6126_, lean_object* v_x_6127_){
_start:
{
lean_object* v_res_6128_; 
v_res_6128_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6125_, v_x_6126_, v_x_6127_);
lean_dec_ref(v_x_6126_);
return v_res_6128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_f_6129_, lean_object* v_as_6130_, lean_object* v_i_6131_, lean_object* v_stop_6132_, lean_object* v_b_6133_){
_start:
{
size_t v_i_boxed_6134_; size_t v_stop_boxed_6135_; lean_object* v_res_6136_; 
v_i_boxed_6134_ = lean_unbox_usize(v_i_6131_);
lean_dec(v_i_6131_);
v_stop_boxed_6135_ = lean_unbox_usize(v_stop_6132_);
lean_dec(v_stop_6132_);
v_res_6136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6129_, v_as_6130_, v_i_boxed_6134_, v_stop_boxed_6135_, v_b_6133_);
lean_dec_ref(v_as_6130_);
return v_res_6136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(lean_object* v_map_6137_, lean_object* v_f_6138_, lean_object* v_init_6139_){
_start:
{
lean_object* v___f_6140_; lean_object* v___x_6141_; 
v___f_6140_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_6140_, 0, v_f_6138_);
v___x_6141_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v___f_6140_, v_map_6137_, v_init_6139_);
return v___x_6141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_map_6142_, lean_object* v_f_6143_, lean_object* v_init_6144_){
_start:
{
lean_object* v_res_6145_; 
v_res_6145_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_6142_, v_f_6143_, v_init_6144_);
lean_dec_ref(v_map_6142_);
return v_res_6145_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(lean_object* v_f_6146_, lean_object* v_init_6147_, lean_object* v_m_6148_){
_start:
{
lean_object* v_map_u2081_6149_; lean_object* v_map_u2082_6150_; lean_object* v_buckets_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; uint8_t v___x_6154_; 
v_map_u2081_6149_ = lean_ctor_get(v_m_6148_, 0);
v_map_u2082_6150_ = lean_ctor_get(v_m_6148_, 1);
v_buckets_6151_ = lean_ctor_get(v_map_u2081_6149_, 1);
v___x_6152_ = lean_unsigned_to_nat(0u);
v___x_6153_ = lean_array_get_size(v_buckets_6151_);
v___x_6154_ = lean_nat_dec_lt(v___x_6152_, v___x_6153_);
if (v___x_6154_ == 0)
{
lean_object* v___x_6155_; 
v___x_6155_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_u2082_6150_, v_f_6146_, v_init_6147_);
return v___x_6155_;
}
else
{
size_t v___x_6156_; size_t v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; 
v___x_6156_ = ((size_t)0ULL);
v___x_6157_ = lean_usize_of_nat(v___x_6153_);
lean_inc(v_f_6146_);
v___x_6158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6146_, v_buckets_6151_, v___x_6156_, v___x_6157_, v_init_6147_);
v___x_6159_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_u2082_6150_, v_f_6146_, v___x_6158_);
return v___x_6159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg___boxed(lean_object* v_f_6160_, lean_object* v_init_6161_, lean_object* v_m_6162_){
_start:
{
lean_object* v_res_6163_; 
v_res_6163_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v_f_6160_, v_init_6161_, v_m_6162_);
lean_dec_ref(v_m_6162_);
return v_res_6163_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(lean_object* v_m_6165_){
_start:
{
lean_object* v___f_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; 
v___f_6166_ = ((lean_object*)(l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0));
v___x_6167_ = lean_box(0);
v___x_6168_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v___f_6166_, v___x_6167_, v_m_6165_);
return v___x_6168_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___boxed(lean_object* v_m_6169_){
_start:
{
lean_object* v_res_6170_; 
v_res_6170_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v_m_6169_);
lean_dec_ref(v_m_6169_);
return v_res_6170_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(lean_object* v_a_6171_, lean_object* v_a_6172_){
_start:
{
if (lean_obj_tag(v_a_6171_) == 0)
{
lean_object* v___x_6173_; 
v___x_6173_ = l_List_reverse___redArg(v_a_6172_);
return v___x_6173_;
}
else
{
lean_object* v_head_6174_; lean_object* v_tail_6175_; lean_object* v___x_6177_; uint8_t v_isShared_6178_; uint8_t v_isSharedCheck_6185_; 
v_head_6174_ = lean_ctor_get(v_a_6171_, 0);
v_tail_6175_ = lean_ctor_get(v_a_6171_, 1);
v_isSharedCheck_6185_ = !lean_is_exclusive(v_a_6171_);
if (v_isSharedCheck_6185_ == 0)
{
v___x_6177_ = v_a_6171_;
v_isShared_6178_ = v_isSharedCheck_6185_;
goto v_resetjp_6176_;
}
else
{
lean_inc(v_tail_6175_);
lean_inc(v_head_6174_);
lean_dec(v_a_6171_);
v___x_6177_ = lean_box(0);
v_isShared_6178_ = v_isSharedCheck_6185_;
goto v_resetjp_6176_;
}
v_resetjp_6176_:
{
uint8_t v___x_6179_; 
v___x_6179_ = l_Lean_Name_isInternal(v_head_6174_);
if (v___x_6179_ == 0)
{
lean_object* v___x_6181_; 
if (v_isShared_6178_ == 0)
{
lean_ctor_set(v___x_6177_, 1, v_a_6172_);
v___x_6181_ = v___x_6177_;
goto v_reusejp_6180_;
}
else
{
lean_object* v_reuseFailAlloc_6183_; 
v_reuseFailAlloc_6183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6183_, 0, v_head_6174_);
lean_ctor_set(v_reuseFailAlloc_6183_, 1, v_a_6172_);
v___x_6181_ = v_reuseFailAlloc_6183_;
goto v_reusejp_6180_;
}
v_reusejp_6180_:
{
v_a_6171_ = v_tail_6175_;
v_a_6172_ = v___x_6181_;
goto _start;
}
}
else
{
lean_del_object(v___x_6177_);
lean_dec(v_head_6174_);
v_a_6171_ = v_tail_6175_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(lean_object* v_a_6186_, lean_object* v_a_6187_){
_start:
{
if (lean_obj_tag(v_a_6186_) == 0)
{
lean_object* v___x_6188_; 
v___x_6188_ = l_List_reverse___redArg(v_a_6187_);
return v___x_6188_;
}
else
{
lean_object* v_head_6189_; lean_object* v_tail_6190_; lean_object* v___x_6192_; uint8_t v_isShared_6193_; uint8_t v_isSharedCheck_6199_; 
v_head_6189_ = lean_ctor_get(v_a_6186_, 0);
v_tail_6190_ = lean_ctor_get(v_a_6186_, 1);
v_isSharedCheck_6199_ = !lean_is_exclusive(v_a_6186_);
if (v_isSharedCheck_6199_ == 0)
{
v___x_6192_ = v_a_6186_;
v_isShared_6193_ = v_isSharedCheck_6199_;
goto v_resetjp_6191_;
}
else
{
lean_inc(v_tail_6190_);
lean_inc(v_head_6189_);
lean_dec(v_a_6186_);
v___x_6192_ = lean_box(0);
v_isShared_6193_ = v_isSharedCheck_6199_;
goto v_resetjp_6191_;
}
v_resetjp_6191_:
{
lean_object* v_fst_6194_; lean_object* v___x_6196_; 
v_fst_6194_ = lean_ctor_get(v_head_6189_, 0);
lean_inc(v_fst_6194_);
lean_dec(v_head_6189_);
if (v_isShared_6193_ == 0)
{
lean_ctor_set(v___x_6192_, 1, v_a_6187_);
lean_ctor_set(v___x_6192_, 0, v_fst_6194_);
v___x_6196_ = v___x_6192_;
goto v_reusejp_6195_;
}
else
{
lean_object* v_reuseFailAlloc_6198_; 
v_reuseFailAlloc_6198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6198_, 0, v_fst_6194_);
lean_ctor_set(v_reuseFailAlloc_6198_, 1, v_a_6187_);
v___x_6196_ = v_reuseFailAlloc_6198_;
goto v_reusejp_6195_;
}
v_reusejp_6195_:
{
v_a_6186_ = v_tail_6190_;
v_a_6187_ = v___x_6196_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv(lean_object* v_env_6200_, lean_object* v_constants_x3f_6201_, lean_object* v_cliOptions_6202_){
_start:
{
lean_object* v___y_6205_; 
if (lean_obj_tag(v_constants_x3f_6201_) == 0)
{
lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; 
lean_inc_ref(v_env_6200_);
v___x_6208_ = l_Lean_Environment_constants(v_env_6200_);
v___x_6209_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v___x_6208_);
lean_dec_ref(v___x_6208_);
v___x_6210_ = lean_box(0);
v___x_6211_ = l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(v___x_6209_, v___x_6210_);
v___x_6212_ = l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(v___x_6211_, v___x_6210_);
v___y_6205_ = v___x_6212_;
goto v___jp_6204_;
}
else
{
lean_object* v_val_6213_; 
v_val_6213_ = lean_ctor_get(v_constants_x3f_6201_, 0);
lean_inc(v_val_6213_);
lean_dec_ref_known(v_constants_x3f_6201_, 1);
v___y_6205_ = v_val_6213_;
goto v___jp_6204_;
}
v___jp_6204_:
{
lean_object* v___f_6206_; lean_object* v___x_6207_; 
lean_inc_ref(v_env_6200_);
v___f_6206_ = lean_alloc_closure((void*)(l_LeanExport_dumpEnv___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6206_, 0, v_env_6200_);
lean_closure_set(v___f_6206_, 1, v_cliOptions_6202_);
lean_closure_set(v___f_6206_, 2, v___y_6205_);
v___x_6207_ = l_LeanExport_M_run___redArg(v_env_6200_, v___f_6206_);
return v___x_6207_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___boxed(lean_object* v_env_6214_, lean_object* v_constants_x3f_6215_, lean_object* v_cliOptions_6216_, lean_object* v_a_6217_){
_start:
{
lean_object* v_res_6218_; 
v_res_6218_ = l_LeanExport_dumpEnv(v_env_6214_, v_constants_x3f_6215_, v_cliOptions_6216_);
return v_res_6218_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(lean_object* v_as_6219_, lean_object* v_as_x27_6220_, lean_object* v_b_6221_, lean_object* v_a_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_){
_start:
{
lean_object* v___x_6226_; 
v___x_6226_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_6220_, v_b_6221_, v___y_6223_, v___y_6224_);
return v___x_6226_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___boxed(lean_object* v_as_6227_, lean_object* v_as_x27_6228_, lean_object* v_b_6229_, lean_object* v_a_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_){
_start:
{
lean_object* v_res_6234_; 
v_res_6234_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(v_as_6227_, v_as_x27_6228_, v_b_6229_, v_a_6230_, v___y_6231_, v___y_6232_);
lean_dec_ref(v___y_6231_);
lean_dec(v_as_x27_6228_);
lean_dec(v_as_6227_);
return v_res_6234_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(lean_object* v_00_u03b2_6235_, lean_object* v_m_6236_){
_start:
{
lean_object* v___x_6237_; 
v___x_6237_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v_m_6236_);
return v___x_6237_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___boxed(lean_object* v_00_u03b2_6238_, lean_object* v_m_6239_){
_start:
{
lean_object* v_res_6240_; 
v_res_6240_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(v_00_u03b2_6238_, v_m_6239_);
lean_dec_ref(v_m_6239_);
return v_res_6240_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(lean_object* v_00_u03b2_6241_, lean_object* v_00_u03c3_6242_, lean_object* v_f_6243_, lean_object* v_init_6244_, lean_object* v_m_6245_){
_start:
{
lean_object* v___x_6246_; 
v___x_6246_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v_f_6243_, v_init_6244_, v_m_6245_);
return v___x_6246_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___boxed(lean_object* v_00_u03b2_6247_, lean_object* v_00_u03c3_6248_, lean_object* v_f_6249_, lean_object* v_init_6250_, lean_object* v_m_6251_){
_start:
{
lean_object* v_res_6252_; 
v_res_6252_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(v_00_u03b2_6247_, v_00_u03c3_6248_, v_f_6249_, v_init_6250_, v_m_6251_);
lean_dec_ref(v_m_6251_);
return v_res_6252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_6253_, lean_object* v_00_u03c3_6254_, lean_object* v_f_6255_, lean_object* v_x_6256_, lean_object* v_x_6257_){
_start:
{
lean_object* v___x_6258_; 
v___x_6258_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(v_f_6255_, v_x_6256_, v_x_6257_);
return v___x_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(lean_object* v_00_u03c3_6259_, lean_object* v_00_u03b2_6260_, lean_object* v_map_6261_, lean_object* v_f_6262_, lean_object* v_init_6263_){
_start:
{
lean_object* v___x_6264_; 
v___x_6264_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_6261_, v_f_6262_, v_init_6263_);
return v___x_6264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03c3_6265_, lean_object* v_00_u03b2_6266_, lean_object* v_map_6267_, lean_object* v_f_6268_, lean_object* v_init_6269_){
_start:
{
lean_object* v_res_6270_; 
v_res_6270_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(v_00_u03c3_6265_, v_00_u03b2_6266_, v_map_6267_, v_f_6268_, v_init_6269_);
lean_dec_ref(v_map_6267_);
return v_res_6270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_6271_, lean_object* v_00_u03c3_6272_, lean_object* v_f_6273_, lean_object* v_as_6274_, size_t v_i_6275_, size_t v_stop_6276_, lean_object* v_b_6277_){
_start:
{
lean_object* v___x_6278_; 
v___x_6278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6273_, v_as_6274_, v_i_6275_, v_stop_6276_, v_b_6277_);
return v___x_6278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_6279_, lean_object* v_00_u03c3_6280_, lean_object* v_f_6281_, lean_object* v_as_6282_, lean_object* v_i_6283_, lean_object* v_stop_6284_, lean_object* v_b_6285_){
_start:
{
size_t v_i_boxed_6286_; size_t v_stop_boxed_6287_; lean_object* v_res_6288_; 
v_i_boxed_6286_ = lean_unbox_usize(v_i_6283_);
lean_dec(v_i_6283_);
v_stop_boxed_6287_ = lean_unbox_usize(v_stop_6284_);
lean_dec(v_stop_6284_);
v_res_6288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(v_00_u03b2_6279_, v_00_u03c3_6280_, v_f_6281_, v_as_6282_, v_i_boxed_6286_, v_stop_boxed_6287_, v_b_6285_);
lean_dec_ref(v_as_6282_);
return v_res_6288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_map_6289_, lean_object* v_f_6290_, lean_object* v_init_6291_){
_start:
{
lean_object* v___x_6292_; 
v___x_6292_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6290_, v_map_6289_, v_init_6291_);
return v___x_6292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_map_6293_, lean_object* v_f_6294_, lean_object* v_init_6295_){
_start:
{
lean_object* v_res_6296_; 
v_res_6296_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(v_map_6293_, v_f_6294_, v_init_6295_);
lean_dec_ref(v_map_6293_);
return v_res_6296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_6297_, lean_object* v_00_u03b2_6298_, lean_object* v_map_6299_, lean_object* v_f_6300_, lean_object* v_init_6301_){
_start:
{
lean_object* v___x_6302_; 
v___x_6302_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6300_, v_map_6299_, v_init_6301_);
return v___x_6302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_6303_, lean_object* v_00_u03b2_6304_, lean_object* v_map_6305_, lean_object* v_f_6306_, lean_object* v_init_6307_){
_start:
{
lean_object* v_res_6308_; 
v_res_6308_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(v_00_u03c3_6303_, v_00_u03b2_6304_, v_map_6305_, v_f_6306_, v_init_6307_);
lean_dec_ref(v_map_6305_);
return v_res_6308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03c3_6309_, lean_object* v_00_u03b1_6310_, lean_object* v_00_u03b2_6311_, lean_object* v_f_6312_, lean_object* v_x_6313_, lean_object* v_x_6314_){
_start:
{
lean_object* v___x_6315_; 
v___x_6315_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6312_, v_x_6313_, v_x_6314_);
return v___x_6315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___boxed(lean_object* v_00_u03c3_6316_, lean_object* v_00_u03b1_6317_, lean_object* v_00_u03b2_6318_, lean_object* v_f_6319_, lean_object* v_x_6320_, lean_object* v_x_6321_){
_start:
{
lean_object* v_res_6322_; 
v_res_6322_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(v_00_u03c3_6316_, v_00_u03b1_6317_, v_00_u03b2_6318_, v_f_6319_, v_x_6320_, v_x_6321_);
lean_dec_ref(v_x_6320_);
return v_res_6322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_6323_, lean_object* v_00_u03b2_6324_, lean_object* v_00_u03c3_6325_, lean_object* v_f_6326_, lean_object* v_as_6327_, size_t v_i_6328_, size_t v_stop_6329_, lean_object* v_b_6330_){
_start:
{
lean_object* v___x_6331_; 
v___x_6331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6326_, v_as_6327_, v_i_6328_, v_stop_6329_, v_b_6330_);
return v___x_6331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_6332_, lean_object* v_00_u03b2_6333_, lean_object* v_00_u03c3_6334_, lean_object* v_f_6335_, lean_object* v_as_6336_, lean_object* v_i_6337_, lean_object* v_stop_6338_, lean_object* v_b_6339_){
_start:
{
size_t v_i_boxed_6340_; size_t v_stop_boxed_6341_; lean_object* v_res_6342_; 
v_i_boxed_6340_ = lean_unbox_usize(v_i_6337_);
lean_dec(v_i_6337_);
v_stop_boxed_6341_ = lean_unbox_usize(v_stop_6338_);
lean_dec(v_stop_6338_);
v_res_6342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(v_00_u03b1_6332_, v_00_u03b2_6333_, v_00_u03c3_6334_, v_f_6335_, v_as_6336_, v_i_boxed_6340_, v_stop_boxed_6341_, v_b_6339_);
lean_dec_ref(v_as_6336_);
return v_res_6342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(lean_object* v_00_u03c3_6343_, lean_object* v_00_u03b1_6344_, lean_object* v_00_u03b2_6345_, lean_object* v_f_6346_, lean_object* v_keys_6347_, lean_object* v_vals_6348_, lean_object* v_heq_6349_, lean_object* v_i_6350_, lean_object* v_acc_6351_){
_start:
{
lean_object* v___x_6352_; 
v___x_6352_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6346_, v_keys_6347_, v_vals_6348_, v_i_6350_, v_acc_6351_);
return v___x_6352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___boxed(lean_object* v_00_u03c3_6353_, lean_object* v_00_u03b1_6354_, lean_object* v_00_u03b2_6355_, lean_object* v_f_6356_, lean_object* v_keys_6357_, lean_object* v_vals_6358_, lean_object* v_heq_6359_, lean_object* v_i_6360_, lean_object* v_acc_6361_){
_start:
{
lean_object* v_res_6362_; 
v_res_6362_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(v_00_u03c3_6353_, v_00_u03b1_6354_, v_00_u03b2_6355_, v_f_6356_, v_keys_6357_, v_vals_6358_, v_heq_6359_, v_i_6360_, v_acc_6361_);
lean_dec_ref(v_vals_6358_);
lean_dec_ref(v_keys_6357_);
return v_res_6362_;
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
