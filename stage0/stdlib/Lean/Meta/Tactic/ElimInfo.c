// Lean compiler output
// Module: Lean.Meta.Tactic.ElimInfo
// Imports: public import Lean.Meta.Check import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
lean_object* l_Array_takeWhile___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static const lean_string_object l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprElimAltInfo_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declName\?"};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numFields"};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14_value;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "provesMotive"};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18_value;
static lean_once_cell_t l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19;
static lean_once_cell_t l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprElimAltInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprElimAltInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprElimAltInfo___closed__0 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprElimAltInfo = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedElimAltInfo_default = (const lean_object*)&l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedElimAltInfo = (const lean_object*)&l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elimExpr"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elimType"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "motivePos"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "targetsPos"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11;
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "altsInfo"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "numComplexMotiveArgs"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprElimInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprElimInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprElimInfo___closed__0 = (const lean_object*)&l_Lean_Meta_instReprElimInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprElimInfo = (const lean_object*)&l_Lean_Meta_instReprElimInfo___closed__0_value;
static const lean_string_object l_Lean_Meta_instInhabitedElimInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_instInhabitedElimInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedElimInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedElimInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedElimInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_instInhabitedElimInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedElimInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedElimInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedElimInfo_default___closed__2;
static const lean_array_object l_Lean_Meta_instInhabitedElimInfo_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedElimInfo_default___closed__3 = (const lean_object*)&l_Lean_Meta_instInhabitedElimInfo_default___closed__3_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedElimInfo_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedElimInfo_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedElimInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedElimInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_altArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_altArity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Motive result type must be a sort, not"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Expected "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = " parameters at motive type, got "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Unexpected eliminator type"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0_value;
static const lean_closure_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isFVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "Expected resulting type of eliminator to be an application of one of its parameters (the motive), but found"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_getElimExprInfo___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getElimExprInfo___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__0 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__0_value;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "induction"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__1 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__1_value;
static const lean_ctor_object l_Lean_Meta_getElimExprInfo___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Meta_getElimExprInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 113, 55, 104, 212, 17, 5, 40)}};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__2 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__2_value;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__3 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__3_value;
static const lean_ctor_object l_Lean_Meta_getElimExprInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__4 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__4_value;
static lean_once_cell_t l_Lean_Meta_getElimExprInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getElimExprInfo___closed__5;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eliminator"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__6 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__6_value;
static lean_once_cell_t l_Lean_Meta_getElimExprInfo___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getElimExprInfo___closed__7;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nhas type"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__8 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__8_value;
static lean_once_cell_t l_Lean_Meta_getElimExprInfo___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getElimExprInfo___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Invalid target:"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Insufficient number of targets for `"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Too many targets for `"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to infer implicit target"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Failed to infer implicit target `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_addImplicitTargets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_addImplicitTargets___closed__0 = (const lean_object*)&l_Lean_Meta_addImplicitTargets___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCustomEliminator_default = (const lean_object*)&l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCustomEliminator = (const lean_object*)&l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(lean_object*);
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1_value),((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "typeNames"};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elimName"};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprCustomEliminator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprCustomEliminator_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprCustomEliminator___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprCustomEliminator = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator___closed__0_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCustomEliminators;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__8_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3;
static lean_once_cell_t l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4;
static const lean_ctor_object l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(lean_object*);
static const lean_string_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "map"};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".toSMap"};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprCustomEliminators___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprCustomEliminators_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprCustomEliminators___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprCustomEliminators = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators___closed__0_value;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminatorEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "customEliminatorExt"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 136, 153, 60, 178, 181, 251, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addCustomEliminatorEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_customEliminatorExt;
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Unexpected eliminator target type"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ElimInfo"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 23, 41, 18, 182, 163, 163, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(97, 22, 214, 90, 248, 223, 62, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 37, 80, 174, 60, 227, 242, 141)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 131, 121, 207, 209, 142, 148, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 30, 84, 209, 139, 131, 70, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 186, 117, 126, 128, 87, 152, 94)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 106, 250, 33, 19, 38, 14, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 152, 58, 59, 147, 212, 205, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 67, 101, 228, 115, 139, 239, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 154, 76, 162, 203, 145, 140, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "induction_eliminator"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 48, 244, 108, 60, 232, 79, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "custom `rec`-like eliminator for the `induction` tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 849, .m_capacity = 849, .m_length = 792, .m_data = "Registers a custom eliminator for the `induction` tactic.\n\nWhenever the types of the targets in an `induction` call matches a custom eliminator, it is used\ninstead of the recursor. This can be useful for redefining the default eliminator to a more useful\none.\n\nExample:\n```lean example\nstructure Three where\n  val : Fin 3\n\nexample (x : Three) (p : Three → Prop) : p x := by\n  induction x\n  -- val : Fin 3 ⊢ p ⟨val⟩\n\n@[induction_eliminator, elab_as_elim]\ndef Three.myRec {motive : Three → Sort u}\n    (zero : motive ⟨0⟩) (one : motive ⟨1⟩) (two : motive ⟨2⟩) :\n    ∀ x, motive x\n  | ⟨0⟩ => zero | ⟨1⟩ => one | ⟨2⟩ => two\n\nexample (x : Three) (p : Three → Prop) : p x := by\n  induction x\n  -- ⊢ p ⟨0⟩\n  -- ⊢ p ⟨1⟩\n  -- ⊢ p ⟨2⟩\n```\n\n`@[cases_eliminator]` works similarly for the `cases` tactic.\n"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)(((size_t)(913872705) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 209, 182, 172, 157, 111, 193, 199)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 254, 161, 0, 64, 194, 151, 2)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 62, 167, 93, 244, 208, 254, 35)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(42, 73, 103, 197, 19, 167, 228, 154)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cases_eliminator"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 14, 239, 189, 147, 54, 173, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "custom `casesOn`-like eliminator for the `cases` tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 849, .m_capacity = 849, .m_length = 792, .m_data = "Registers a custom eliminator for the `cases` tactic.\n\nWhenever the types of the targets in an `cases` call matches a custom eliminator, it is used\ninstead of the `casesOn` eliminator. This can be useful for redefining the default eliminator to a\nmore useful one.\n\nExample:\n```lean example\nstructure Three where\n  val : Fin 3\n\nexample (x : Three) (p : Three → Prop) : p x := by\n  cases x\n  -- val : Fin 3 ⊢ p ⟨val⟩\n\n@[cases_eliminator, elab_as_elim]\ndef Three.myRec {motive : Three → Sort u}\n    (zero : motive ⟨0⟩) (one : motive ⟨1⟩) (two : motive ⟨2⟩) :\n    ∀ x, motive x\n  | ⟨0⟩ => zero | ⟨1⟩ => one | ⟨2⟩ => two\n\nexample (x : Three) (p : Three → Prop) : p x := by\n  cases x\n  -- ⊢ p ⟨0⟩\n  -- ⊢ p ⟨1⟩\n  -- ⊢ p ⟨2⟩\n```\n\n`@[induction_eliminator]` works similarly for the `induction` tactic.\n"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_getCustomEliminator_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_addImplicitTargets___closed__0_value)}};
static const lean_object* l_Lean_Meta_getCustomEliminator_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getCustomEliminator_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_7_) == 0)
{
lean_object* v___x_9_; 
v___x_9_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1));
return v___x_9_;
}
else
{
lean_object* v_val_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_val_10_ = lean_ctor_get(v_x_7_, 0);
lean_inc(v_val_10_);
lean_dec_ref_known(v_x_7_, 1);
v___x_11_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3));
v___x_12_ = lean_unsigned_to_nat(1024u);
v___x_13_ = l_Lean_Name_reprPrec(v_val_10_, v___x_12_);
v___x_14_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_11_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
v___x_15_ = l_Repr_addAppParen(v___x_14_, v_x_8_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(v_x_16_, v_x_17_);
lean_dec(v_x_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprElimAltInfo_repr_spec__1(lean_object* v_a_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_nat_to_int(v_a_19_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(8u);
v___x_35_ = lean_nat_to_int(v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(13u);
v___x_43_ = lean_nat_to_int(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(16u);
v___x_51_ = lean_nat_to_int(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0));
v___x_54_ = lean_string_length(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19);
v___x_56_ = lean_nat_to_int(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg(lean_object* v_x_61_){
_start:
{
lean_object* v_name_62_; lean_object* v_declName_x3f_63_; lean_object* v_numFields_64_; uint8_t v_provesMotive_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_name_62_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_name_62_);
v_declName_x3f_63_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_declName_x3f_63_);
v_numFields_64_ = lean_ctor_get(v_x_61_, 2);
lean_inc(v_numFields_64_);
v_provesMotive_65_ = lean_ctor_get_uint8(v_x_61_, sizeof(void*)*3);
lean_dec_ref(v_x_61_);
v___x_66_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5));
v___x_67_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6));
v___x_68_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = l_Lean_Name_reprPrec(v_name_62_, v___x_69_);
v___x_71_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_68_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = 0;
v___x_73_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*1, v___x_72_);
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_67_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9));
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_box(1);
v___x_78_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11));
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_66_);
v___x_82_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12);
v___x_83_ = l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(v_declName_x3f_63_, v___x_69_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___x_72_);
v___x_86_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_81_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_75_);
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_77_);
v___x_89_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14));
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_66_);
v___x_92_ = l_Nat_reprFast(v_numFields_64_);
v___x_93_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_82_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_72_);
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_91_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_75_);
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_77_);
v___x_99_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16));
v___x_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_66_);
v___x_102_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17);
v___x_103_ = l_Bool_repr___redArg(v_provesMotive_65_);
v___x_104_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*1, v___x_72_);
v___x_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_101_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_108_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_106_);
v___x_110_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_107_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_72_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr(lean_object* v_x_114_, lean_object* v_prec_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_x_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr___boxed(lean_object* v_x_117_, lean_object* v_prec_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Meta_instReprElimAltInfo_repr(v_x_117_, v_prec_118_);
lean_dec(v_prec_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(lean_object* v___y_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = l_Nat_reprFast(v___y_129_);
v___x_131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_dec(v_x_132_);
return v_x_133_;
}
else
{
lean_object* v_head_135_; lean_object* v_tail_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_147_; 
v_head_135_ = lean_ctor_get(v_x_134_, 0);
v_tail_136_ = lean_ctor_get(v_x_134_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_134_);
if (v_isSharedCheck_147_ == 0)
{
v___x_138_ = v_x_134_;
v_isShared_139_ = v_isSharedCheck_147_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_tail_136_);
lean_inc(v_head_135_);
lean_dec(v_x_134_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_147_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
lean_inc(v_x_132_);
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 5);
lean_ctor_set(v___x_138_, 1, v_x_132_);
lean_ctor_set(v___x_138_, 0, v_x_133_);
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_x_133_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_x_132_);
v___x_141_ = v_reuseFailAlloc_146_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = l_Nat_reprFast(v_head_135_);
v___x_143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_141_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v_x_133_ = v___x_144_;
v_x_134_ = v_tail_136_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1(lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_dec(v_x_148_);
return v_x_149_;
}
else
{
lean_object* v_head_151_; lean_object* v_tail_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_163_; 
v_head_151_ = lean_ctor_get(v_x_150_, 0);
v_tail_152_ = lean_ctor_get(v_x_150_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_150_);
if (v_isSharedCheck_163_ == 0)
{
v___x_154_ = v_x_150_;
v_isShared_155_ = v_isSharedCheck_163_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_tail_152_);
lean_inc(v_head_151_);
lean_dec(v_x_150_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_163_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
lean_inc(v_x_148_);
if (v_isShared_155_ == 0)
{
lean_ctor_set_tag(v___x_154_, 5);
lean_ctor_set(v___x_154_, 1, v_x_148_);
lean_ctor_set(v___x_154_, 0, v_x_149_);
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_x_149_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_x_148_);
v___x_157_ = v_reuseFailAlloc_162_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_158_ = l_Nat_reprFast(v_head_151_);
v___x_159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
v___x_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_157_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(v_x_148_, v___x_160_, v_tail_152_);
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0(lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v___x_166_; 
lean_dec(v_x_165_);
v___x_166_ = lean_box(0);
return v___x_166_;
}
else
{
lean_object* v_tail_167_; 
v_tail_167_ = lean_ctor_get(v_x_164_, 1);
if (lean_obj_tag(v_tail_167_) == 0)
{
lean_object* v_head_168_; lean_object* v___x_169_; 
lean_dec(v_x_165_);
v_head_168_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_head_168_);
lean_dec_ref_known(v_x_164_, 2);
v___x_169_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(v_head_168_);
return v___x_169_;
}
else
{
lean_object* v_head_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_inc(v_tail_167_);
v_head_170_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_head_170_);
lean_dec_ref_known(v_x_164_, 2);
v___x_171_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(v_head_170_);
v___x_172_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1(v_x_165_, v___x_171_, v_tail_167_);
return v___x_172_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0));
v___x_179_ = lean_string_length(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0(lean_object* v_xs_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_190_ = lean_array_get_size(v_xs_189_);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_nat_dec_eq(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_193_ = lean_array_to_list(v_xs_189_);
v___x_194_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_195_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0(v___x_193_, v___x_194_);
v___x_196_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4);
v___x_197_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5));
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_195_);
v___x_199_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_196_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = l_Std_Format_fill(v___x_201_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; 
lean_dec_ref(v_xs_189_);
v___x_203_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8));
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
lean_dec(v_x_204_);
return v_x_205_;
}
else
{
lean_object* v_head_207_; lean_object* v_tail_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_218_; 
v_head_207_ = lean_ctor_get(v_x_206_, 0);
v_tail_208_ = lean_ctor_get(v_x_206_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_218_ == 0)
{
v___x_210_ = v_x_206_;
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_tail_208_);
lean_inc(v_head_207_);
lean_dec(v_x_206_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
lean_inc(v_x_204_);
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 5);
lean_ctor_set(v___x_210_, 1, v_x_204_);
lean_ctor_set(v___x_210_, 0, v_x_205_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_x_205_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_x_204_);
v___x_213_ = v_reuseFailAlloc_217_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_207_);
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v_x_205_ = v___x_215_;
v_x_206_ = v_tail_208_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4(lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
lean_dec(v_x_219_);
return v_x_220_;
}
else
{
lean_object* v_head_222_; lean_object* v_tail_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_233_; 
v_head_222_ = lean_ctor_get(v_x_221_, 0);
v_tail_223_ = lean_ctor_get(v_x_221_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_233_ == 0)
{
v___x_225_ = v_x_221_;
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_tail_223_);
lean_inc(v_head_222_);
lean_dec(v_x_221_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
lean_inc(v_x_219_);
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 5);
lean_ctor_set(v___x_225_, 1, v_x_219_);
lean_ctor_set(v___x_225_, 0, v_x_220_);
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_x_220_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_x_219_);
v___x_228_ = v_reuseFailAlloc_232_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_222_);
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4_spec__6(v_x_219_, v___x_230_, v_tail_223_);
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v___x_236_; 
lean_dec(v_x_235_);
v___x_236_ = lean_box(0);
return v___x_236_;
}
else
{
lean_object* v_tail_237_; 
v_tail_237_ = lean_ctor_get(v_x_234_, 1);
if (lean_obj_tag(v_tail_237_) == 0)
{
lean_object* v_head_238_; lean_object* v___x_239_; 
lean_dec(v_x_235_);
v_head_238_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_head_238_);
lean_dec_ref_known(v_x_234_, 2);
v___x_239_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_238_);
return v___x_239_;
}
else
{
lean_object* v_head_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc(v_tail_237_);
v_head_240_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_head_240_);
lean_dec_ref_known(v_x_234_, 2);
v___x_241_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_240_);
v___x_242_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4(v_x_235_, v___x_241_, v_tail_237_);
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1(lean_object* v_xs_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_array_get_size(v_xs_243_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_nat_dec_eq(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_247_ = lean_array_to_list(v_xs_243_);
v___x_248_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_249_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2(v___x_247_, v___x_248_);
v___x_250_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4);
v___x_251_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5));
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_249_);
v___x_253_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_250_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = l_Std_Format_fill(v___x_255_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; 
lean_dec_ref(v_xs_243_);
v___x_257_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8));
return v___x_257_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(12u);
v___x_268_ = lean_nat_to_int(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(14u);
v___x_279_ = lean_nat_to_int(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(24u);
v___x_287_ = lean_nat_to_int(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg(lean_object* v_x_288_){
_start:
{
lean_object* v_elimExpr_289_; lean_object* v_elimType_290_; lean_object* v_motivePos_291_; lean_object* v_targetsPos_292_; lean_object* v_altsInfo_293_; lean_object* v_numComplexMotiveArgs_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_elimExpr_289_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_elimExpr_289_);
v_elimType_290_ = lean_ctor_get(v_x_288_, 1);
lean_inc_ref(v_elimType_290_);
v_motivePos_291_ = lean_ctor_get(v_x_288_, 2);
lean_inc(v_motivePos_291_);
v_targetsPos_292_ = lean_ctor_get(v_x_288_, 3);
lean_inc_ref(v_targetsPos_292_);
v_altsInfo_293_ = lean_ctor_get(v_x_288_, 4);
lean_inc_ref(v_altsInfo_293_);
v_numComplexMotiveArgs_294_ = lean_ctor_get(v_x_288_, 5);
lean_inc(v_numComplexMotiveArgs_294_);
lean_dec_ref(v_x_288_);
v___x_295_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5));
v___x_296_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3));
v___x_297_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = l_Lean_instReprExpr_repr(v_elimExpr_289_, v___x_298_);
v___x_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_297_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = 0;
v___x_302_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*1, v___x_301_);
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_296_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9));
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_box(1);
v___x_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6));
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_295_);
v___x_311_ = l_Lean_instReprExpr_repr(v_elimType_290_, v___x_298_);
v___x_312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_297_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_301_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_310_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_304_);
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_306_);
v___x_317_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8));
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_295_);
v___x_320_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12);
v___x_321_ = l_Nat_reprFast(v_motivePos_291_);
v___x_322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___x_323_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_320_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*1, v___x_301_);
v___x_325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_319_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_304_);
v___x_327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_306_);
v___x_328_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10));
v___x_329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_295_);
v___x_331_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11);
v___x_332_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0(v_targetsPos_292_);
v___x_333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_301_);
v___x_335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_330_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_304_);
v___x_337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_306_);
v___x_338_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13));
v___x_339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_295_);
v___x_341_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1(v_altsInfo_293_);
v___x_342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_297_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*1, v___x_301_);
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_340_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_304_);
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_306_);
v___x_347_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15));
v___x_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_295_);
v___x_350_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16);
v___x_351_ = l_Nat_reprFast(v_numComplexMotiveArgs_294_);
v___x_352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
v___x_353_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_350_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_301_);
v___x_355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_349_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_357_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_355_);
v___x_359_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_356_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*1, v___x_301_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr(lean_object* v_x_363_, lean_object* v_prec_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_instReprElimInfo_repr___redArg(v_x_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr___boxed(lean_object* v_x_366_, lean_object* v_prec_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_instReprElimInfo_repr(v_x_366_, v_prec_367_);
lean_dec(v_prec_367_);
return v_res_368_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__2(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_box(0);
v___x_375_ = ((lean_object*)(l_Lean_Meta_instInhabitedElimInfo_default___closed__1));
v___x_376_ = l_Lean_Expr_const___override(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__4(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_379_ = ((lean_object*)(l_Lean_Meta_instInhabitedElimInfo_default___closed__3));
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_obj_once(&l_Lean_Meta_instInhabitedElimInfo_default___closed__2, &l_Lean_Meta_instInhabitedElimInfo_default___closed__2_once, _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__2);
v___x_382_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
lean_ctor_set(v___x_382_, 2, v___x_380_);
lean_ctor_set(v___x_382_, 3, v___x_379_);
lean_ctor_set(v___x_382_, 4, v___x_379_);
lean_ctor_set(v___x_382_, 5, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedElimInfo_default(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_obj_once(&l_Lean_Meta_instInhabitedElimInfo_default___closed__4, &l_Lean_Meta_instInhabitedElimInfo_default___closed__4_once, _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__4);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedElimInfo(void){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_instInhabitedElimInfo_default;
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_altArity(lean_object* v_motive_385_, lean_object* v_n_386_, lean_object* v_x_387_){
_start:
{
switch(lean_obj_tag(v_x_387_))
{
case 7:
{
lean_object* v_body_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_body_388_ = lean_ctor_get(v_x_387_, 2);
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v_n_386_, v___x_389_);
lean_dec(v_n_386_);
v_n_386_ = v___x_390_;
v_x_387_ = v_body_388_;
goto _start;
}
case 8:
{
lean_object* v_body_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_body_392_ = lean_ctor_get(v_x_387_, 3);
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_n_386_, v___x_393_);
lean_dec(v_n_386_);
v_n_386_ = v___x_394_;
v_x_387_ = v_body_392_;
goto _start;
}
default: 
{
lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_396_ = l_Lean_Expr_getAppFn(v_x_387_);
v___x_397_ = lean_expr_eqv(v___x_396_, v_motive_385_);
lean_dec_ref(v___x_396_);
v___x_398_ = lean_box(v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_n_386_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_altArity___boxed(lean_object* v_motive_400_, lean_object* v_n_401_, lean_object* v_x_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Meta_altArity(v_motive_400_, v_n_401_, v_x_402_);
lean_dec_ref(v_x_402_);
lean_dec_ref(v_motive_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0(lean_object* v_k_404_, lean_object* v_b_405_, lean_object* v_c_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
lean_inc(v___y_410_);
lean_inc_ref(v___y_409_);
lean_inc(v___y_408_);
lean_inc_ref(v___y_407_);
v___x_412_ = lean_apply_7(v_k_404_, v_b_405_, v_c_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, lean_box(0));
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0___boxed(lean_object* v_k_413_, lean_object* v_b_414_, lean_object* v_c_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0(v_k_413_, v_b_414_, v_c_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(lean_object* v_type_422_, lean_object* v_k_423_, uint8_t v_cleanupAnnotations_424_, uint8_t v_whnfType_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___f_431_; lean_object* v___x_432_; 
v___f_431_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_431_, 0, v_k_423_);
v___x_432_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_422_, v___f_431_, v_cleanupAnnotations_424_, v_whnfType_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_432_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_432_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___boxed(lean_object* v_type_449_, lean_object* v_k_450_, lean_object* v_cleanupAnnotations_451_, lean_object* v_whnfType_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_458_; uint8_t v_whnfType_boxed_459_; lean_object* v_res_460_; 
v_cleanupAnnotations_boxed_458_ = lean_unbox(v_cleanupAnnotations_451_);
v_whnfType_boxed_459_ = lean_unbox(v_whnfType_452_);
v_res_460_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_type_449_, v_k_450_, v_cleanupAnnotations_boxed_458_, v_whnfType_boxed_459_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2(lean_object* v_00_u03b1_461_, lean_object* v_type_462_, lean_object* v_k_463_, uint8_t v_cleanupAnnotations_464_, uint8_t v_whnfType_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_type_462_, v_k_463_, v_cleanupAnnotations_464_, v_whnfType_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___boxed(lean_object* v_00_u03b1_472_, lean_object* v_type_473_, lean_object* v_k_474_, lean_object* v_cleanupAnnotations_475_, lean_object* v_whnfType_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_482_; uint8_t v_whnfType_boxed_483_; lean_object* v_res_484_; 
v_cleanupAnnotations_boxed_482_ = lean_unbox(v_cleanupAnnotations_475_);
v_whnfType_boxed_483_ = lean_unbox(v_whnfType_476_);
v_res_484_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2(v_00_u03b1_472_, v_type_473_, v_k_474_, v_cleanupAnnotations_boxed_482_, v_whnfType_boxed_483_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(lean_object* v_msgData_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; lean_object* v_env_492_; lean_object* v___x_493_; lean_object* v_mctx_494_; lean_object* v_lctx_495_; lean_object* v_options_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_491_ = lean_st_ref_get(v___y_489_);
v_env_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_env_492_);
lean_dec(v___x_491_);
v___x_493_ = lean_st_ref_get(v___y_487_);
v_mctx_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_mctx_494_);
lean_dec(v___x_493_);
v_lctx_495_ = lean_ctor_get(v___y_486_, 2);
v_options_496_ = lean_ctor_get(v___y_488_, 2);
lean_inc_ref(v_options_496_);
lean_inc_ref(v_lctx_495_);
v___x_497_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_497_, 0, v_env_492_);
lean_ctor_set(v___x_497_, 1, v_mctx_494_);
lean_ctor_set(v___x_497_, 2, v_lctx_495_);
lean_ctor_set(v___x_497_, 3, v_options_496_);
v___x_498_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_msgData_485_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2___boxed(lean_object* v_msgData_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msgData_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_ref_513_; lean_object* v___x_514_; lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_ref_513_ = lean_ctor_get(v___y_510_, 5);
v___x_514_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_inc(v_ref_513_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_ref_513_);
lean_ctor_set(v___x_519_, 1, v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 1);
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg___boxed(lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(lean_object* v_a_543_, lean_object* v_x_544_, lean_object* v_motiveParams_545_, lean_object* v_motiveResultType_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_560_ = lean_array_get_size(v_motiveParams_545_);
v___x_561_ = lean_array_get_size(v_x_544_);
v___x_562_ = lean_nat_dec_eq(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_563_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3);
v___x_564_ = l_Nat_reprFast(v___x_561_);
v___x_565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___x_566_ = l_Lean_MessageData_ofFormat(v___x_565_);
v___x_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_563_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5);
v___x_569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l_Nat_reprFast(v___x_560_);
v___x_571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___x_572_ = l_Lean_MessageData_ofFormat(v___x_571_);
v___x_573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_569_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = l_Lean_indentExpr(v_a_543_);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_577_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_578_;
}
else
{
goto v___jp_552_;
}
v___jp_552_:
{
uint8_t v___x_553_; 
v___x_553_ = l_Lean_Expr_isSort(v_motiveResultType_546_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_554_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1);
v___x_555_ = l_Lean_indentExpr(v_a_543_);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_556_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec_ref(v_a_543_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed(lean_object* v_a_579_, lean_object* v_x_580_, lean_object* v_motiveParams_581_, lean_object* v_motiveResultType_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(v_a_579_, v_x_580_, v_motiveParams_581_, v_motiveResultType_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec_ref(v_motiveResultType_582_);
lean_dec_ref(v_motiveParams_581_);
lean_dec_ref(v_x_580_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(lean_object* v_xs_589_, lean_object* v_v_590_, lean_object* v_i_591_){
_start:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_array_get_size(v_xs_589_);
v___x_593_ = lean_nat_dec_lt(v_i_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
lean_dec(v_i_591_);
v___x_594_ = lean_box(0);
return v___x_594_;
}
else
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_array_fget_borrowed(v_xs_589_, v_i_591_);
v___x_596_ = lean_expr_eqv(v___x_595_, v_v_590_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_i_591_, v___x_597_);
lean_dec(v_i_591_);
v_i_591_ = v___x_598_;
goto _start;
}
else
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_i_591_);
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2___boxed(lean_object* v_xs_601_, lean_object* v_v_602_, lean_object* v_i_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(v_xs_601_, v_v_602_, v_i_603_);
lean_dec_ref(v_v_602_);
lean_dec_ref(v_xs_601_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(lean_object* v_xs_605_, lean_object* v_v_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(v_xs_605_, v_v_606_, v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0___boxed(lean_object* v_xs_609_, lean_object* v_v_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(v_xs_609_, v_v_610_);
lean_dec_ref(v_v_610_);
lean_dec_ref(v_xs_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(lean_object* v_xs_612_, lean_object* v_v_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(v_xs_612_, v_v_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v___x_615_; 
v___x_615_ = lean_box(0);
return v___x_615_;
}
else
{
lean_object* v_val_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_val_616_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_614_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_val_616_);
lean_dec(v___x_614_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_val_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0___boxed(lean_object* v_xs_624_, lean_object* v_v_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_624_, v_v_625_);
lean_dec_ref(v_v_625_);
lean_dec_ref(v_xs_624_);
return v_res_626_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(lean_object* v_xs_630_, lean_object* v_a_631_, size_t v_sz_632_, size_t v_i_633_, lean_object* v_bs_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_lt(v_i_633_, v_sz_632_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v_a_631_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v_bs_634_);
return v___x_641_;
}
else
{
lean_object* v_v_642_; lean_object* v___x_643_; lean_object* v_bs_x27_644_; lean_object* v_a_646_; lean_object* v___x_651_; 
v_v_642_ = lean_array_uget(v_bs_634_, v_i_633_);
v___x_643_ = lean_unsigned_to_nat(0u);
v_bs_x27_644_ = lean_array_uset(v_bs_634_, v_i_633_, v___x_643_);
v___x_651_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_630_, v_v_642_);
lean_dec(v_v_642_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
lean_inc_ref(v_a_631_);
v___x_653_ = l_Lean_indentExpr(v_a_631_);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_654_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v_a_646_ = v_a_656_;
goto v___jp_645_;
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v_bs_x27_644_);
lean_dec_ref(v_a_631_);
v_a_657_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_655_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_object* v_val_665_; 
v_val_665_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v___x_651_, 1);
v_a_646_ = v_val_665_;
goto v___jp_645_;
}
v___jp_645_:
{
size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_633_, v___x_647_);
v___x_649_ = lean_array_uset(v_bs_x27_644_, v_i_633_, v_a_646_);
v_i_633_ = v___x_648_;
v_bs_634_ = v___x_649_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___boxed(lean_object* v_xs_666_, lean_object* v_a_667_, lean_object* v_sz_668_, lean_object* v_i_669_, lean_object* v_bs_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
size_t v_sz_boxed_676_; size_t v_i_boxed_677_; lean_object* v_res_678_; 
v_sz_boxed_676_ = lean_unbox_usize(v_sz_668_);
lean_dec(v_sz_668_);
v_i_boxed_677_ = lean_unbox_usize(v_i_669_);
lean_dec(v_i_669_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_666_, v_a_667_, v_sz_boxed_676_, v_i_boxed_677_, v_bs_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v_xs_666_);
return v_res_678_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(lean_object* v_a_679_, lean_object* v_as_680_, size_t v_i_681_, size_t v_stop_682_){
_start:
{
uint8_t v___x_683_; 
v___x_683_ = lean_usize_dec_eq(v_i_681_, v_stop_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_array_uget_borrowed(v_as_680_, v_i_681_);
v___x_685_ = lean_expr_eqv(v_a_679_, v___x_684_);
if (v___x_685_ == 0)
{
size_t v___x_686_; size_t v___x_687_; 
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_add(v_i_681_, v___x_686_);
v_i_681_ = v___x_687_;
goto _start;
}
else
{
return v___x_685_;
}
}
else
{
uint8_t v___x_689_; 
v___x_689_ = 0;
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6___boxed(lean_object* v_a_690_, lean_object* v_as_691_, lean_object* v_i_692_, lean_object* v_stop_693_){
_start:
{
size_t v_i_boxed_694_; size_t v_stop_boxed_695_; uint8_t v_res_696_; lean_object* v_r_697_; 
v_i_boxed_694_ = lean_unbox_usize(v_i_692_);
lean_dec(v_i_692_);
v_stop_boxed_695_ = lean_unbox_usize(v_stop_693_);
lean_dec(v_stop_693_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(v_a_690_, v_as_691_, v_i_boxed_694_, v_stop_boxed_695_);
lean_dec_ref(v_as_691_);
lean_dec_ref(v_a_690_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(lean_object* v_as_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_array_get_size(v_as_698_);
v___x_702_ = lean_nat_dec_lt(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
return v___x_702_;
}
else
{
if (v___x_702_ == 0)
{
return v___x_702_;
}
else
{
size_t v___x_703_; size_t v___x_704_; uint8_t v___x_705_; 
v___x_703_ = ((size_t)0ULL);
v___x_704_ = lean_usize_of_nat(v___x_701_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(v_a_699_, v_as_698_, v___x_703_, v___x_704_);
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4___boxed(lean_object* v_as_706_, lean_object* v_a_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(v_as_706_, v_a_707_);
lean_dec_ref(v_a_707_);
lean_dec_ref(v_as_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(lean_object* v_upperBound_710_, lean_object* v_xs_711_, lean_object* v_motive_712_, lean_object* v___x_713_, lean_object* v_baseDeclName_x3f_714_, lean_object* v___x_715_, lean_object* v_a_716_, lean_object* v_b_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_a_723_; uint8_t v___x_727_; 
v___x_727_ = lean_nat_dec_lt(v_a_716_, v_upperBound_710_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
lean_dec(v_a_716_);
lean_dec_ref(v___x_715_);
lean_dec(v_baseDeclName_x3f_714_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v_b_717_);
return v___x_728_;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_array_fget_borrowed(v_xs_711_, v_a_716_);
v___x_730_ = lean_expr_eqv(v___x_729_, v_motive_712_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
v___x_731_ = l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(v___x_713_, v___x_729_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = l_Lean_Expr_fvarId_x21(v___x_729_);
v___x_733_ = l_Lean_FVarId_getDecl___redArg(v___x_732_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; uint8_t v___x_735_; uint8_t v___x_736_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Lean_LocalDecl_binderInfo(v_a_734_);
v___x_736_ = l_Lean_BinderInfo_isExplicit(v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v_a_734_);
v_a_723_ = v_b_717_;
goto v___jp_722_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_fst_740_; lean_object* v_snd_741_; lean_object* v___x_742_; lean_object* v___y_744_; 
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = l_Lean_LocalDecl_type(v_a_734_);
v___x_739_ = l_Lean_Meta_altArity(v_motive_712_, v___x_737_, v___x_738_);
lean_dec_ref(v___x_738_);
v_fst_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_fst_740_);
v_snd_741_ = lean_ctor_get(v___x_739_, 1);
lean_inc(v_snd_741_);
lean_dec_ref(v___x_739_);
v___x_742_ = l_Lean_LocalDecl_userName(v_a_734_);
lean_dec(v_a_734_);
if (lean_obj_tag(v_baseDeclName_x3f_714_) == 0)
{
v___y_744_ = v_baseDeclName_x3f_714_;
goto v___jp_743_;
}
else
{
lean_object* v_val_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_val_748_ = lean_ctor_get(v_baseDeclName_x3f_714_, 0);
lean_inc(v___x_742_);
lean_inc(v_val_748_);
v___x_749_ = l_Lean_Name_append(v_val_748_, v___x_742_);
lean_inc(v___x_749_);
lean_inc_ref(v___x_715_);
v___x_750_ = l_Lean_Environment_contains(v___x_715_, v___x_749_, v___x_736_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
lean_dec(v___x_749_);
v___x_751_ = lean_box(0);
v___y_744_ = v___x_751_;
goto v___jp_743_;
}
else
{
lean_object* v___x_752_; 
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_749_);
v___y_744_ = v___x_752_;
goto v___jp_743_;
}
}
v___jp_743_:
{
lean_object* v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_745_, 0, v___x_742_);
lean_ctor_set(v___x_745_, 1, v___y_744_);
lean_ctor_set(v___x_745_, 2, v_fst_740_);
v___x_746_ = lean_unbox(v_snd_741_);
lean_dec(v_snd_741_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*3, v___x_746_);
v___x_747_ = lean_array_push(v_b_717_, v___x_745_);
v_a_723_ = v___x_747_;
goto v___jp_722_;
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v_b_717_);
lean_dec(v_a_716_);
lean_dec_ref(v___x_715_);
lean_dec(v_baseDeclName_x3f_714_);
v_a_753_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_733_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_733_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
v_a_723_ = v_b_717_;
goto v___jp_722_;
}
}
else
{
v_a_723_ = v_b_717_;
goto v___jp_722_;
}
}
v___jp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_a_716_, v___x_724_);
lean_dec(v_a_716_);
v_a_716_ = v___x_725_;
v_b_717_ = v_a_723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg___boxed(lean_object* v_upperBound_761_, lean_object* v_xs_762_, lean_object* v_motive_763_, lean_object* v___x_764_, lean_object* v_baseDeclName_x3f_765_, lean_object* v___x_766_, lean_object* v_a_767_, lean_object* v_b_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v_upperBound_761_, v_xs_762_, v_motive_763_, v___x_764_, v_baseDeclName_x3f_765_, v___x_766_, v_a_767_, v_b_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec_ref(v___x_764_);
lean_dec_ref(v_motive_763_);
lean_dec_ref(v_xs_762_);
lean_dec(v_upperBound_761_);
return v_res_773_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(lean_object* v_xs_780_, lean_object* v_a_781_, lean_object* v_elimExpr_782_, lean_object* v_baseDeclName_x3f_783_, lean_object* v_type_784_, lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; 
if (lean_obj_tag(v_x_785_) == 5)
{
lean_object* v_fn_868_; lean_object* v_arg_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_fn_868_ = lean_ctor_get(v_x_785_, 0);
lean_inc_ref(v_fn_868_);
v_arg_869_ = lean_ctor_get(v_x_785_, 1);
lean_inc_ref(v_arg_869_);
lean_dec_ref_known(v_x_785_, 2);
v___x_870_ = lean_array_set(v_x_786_, v_x_787_, v_arg_869_);
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_sub(v_x_787_, v___x_871_);
lean_dec(v_x_787_);
v_x_785_ = v_fn_868_;
v_x_786_ = v___x_870_;
v_x_787_ = v___x_872_;
goto _start;
}
else
{
lean_object* v___f_874_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; uint8_t v___x_887_; 
lean_dec(v_x_787_);
v___f_874_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1));
v___x_887_ = l_Lean_Expr_isFVar(v_x_785_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_baseDeclName_x3f_783_);
lean_dec_ref(v_elimExpr_782_);
lean_dec_ref(v_a_781_);
v___x_888_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3);
v___x_889_ = l_Lean_indentExpr(v_type_784_);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_890_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
else
{
lean_dec_ref(v_type_784_);
v___y_876_ = v___y_788_;
v___y_877_ = v___y_789_;
v___y_878_ = v___y_790_;
v___y_879_ = v___y_791_;
goto v___jp_875_;
}
v___jp_875_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_880_ = l_Array_takeWhile___redArg(v___f_874_, v_x_786_);
v___x_881_ = lean_array_get_size(v___x_880_);
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_array_get_size(v_x_786_);
v___x_884_ = lean_nat_dec_le(v___x_881_, v___x_882_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_881_);
lean_ctor_set(v___x_885_, 1, v___x_883_);
v___y_794_ = v___y_878_;
v___y_795_ = v___y_876_;
v___y_796_ = v___y_879_;
v___y_797_ = v___x_880_;
v___y_798_ = v___y_877_;
v___y_799_ = v___x_885_;
goto v___jp_793_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_882_);
lean_ctor_set(v___x_886_, 1, v___x_883_);
v___y_794_ = v___y_878_;
v___y_795_ = v___y_876_;
v___y_796_ = v___y_879_;
v___y_797_ = v___x_880_;
v___y_798_ = v___y_877_;
v___y_799_ = v___x_886_;
goto v___jp_793_;
}
}
}
v___jp_793_:
{
lean_object* v___x_800_; 
lean_inc(v___y_796_);
lean_inc_ref(v___y_794_);
lean_inc(v___y_798_);
lean_inc_ref(v___y_795_);
lean_inc_ref(v_x_785_);
v___x_800_ = lean_infer_type(v_x_785_, v___y_795_, v___y_798_, v___y_794_, v___y_796_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___f_802_; uint8_t v___x_803_; lean_object* v___x_804_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc_n(v_a_801_, 2);
lean_dec_ref_known(v___x_800_, 1);
lean_inc_ref(v_x_786_);
v___f_802_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed), 9, 2);
lean_closure_set(v___f_802_, 0, v_a_801_);
lean_closure_set(v___f_802_, 1, v_x_786_);
v___x_803_ = 0;
v___x_804_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_801_, v___f_802_, v___x_803_, v___x_803_, v___y_795_, v___y_798_, v___y_794_, v___y_796_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v___x_805_; 
lean_dec_ref_known(v___x_804_, 1);
v___x_805_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_780_, v_x_785_);
if (lean_obj_tag(v___x_805_) == 1)
{
lean_object* v_val_806_; size_t v_sz_807_; size_t v___x_808_; lean_object* v___x_809_; 
v_val_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v___x_805_, 1);
v_sz_807_ = lean_array_size(v___y_797_);
v___x_808_ = ((size_t)0ULL);
lean_inc_ref(v___y_797_);
lean_inc_ref(v_a_781_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_780_, v_a_781_, v_sz_807_, v___x_808_, v___y_797_, v___y_795_, v___y_798_, v___y_794_, v___y_796_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; lean_object* v_lower_812_; lean_object* v_upper_813_; lean_object* v_env_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v___x_811_ = lean_st_ref_get(v___y_796_);
v_lower_812_ = lean_ctor_get(v___y_799_, 0);
lean_inc(v_lower_812_);
v_upper_813_ = lean_ctor_get(v___y_799_, 1);
lean_inc(v_upper_813_);
lean_dec_ref(v___y_799_);
v_env_814_ = lean_ctor_get(v___x_811_, 0);
lean_inc_ref(v_env_814_);
lean_dec(v___x_811_);
v___x_815_ = lean_array_get_size(v_xs_780_);
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0));
v___x_818_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v___x_815_, v_xs_780_, v_x_785_, v___y_797_, v_baseDeclName_x3f_783_, v_env_814_, v___x_816_, v___x_817_, v___y_795_, v___y_794_, v___y_796_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_x_785_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_831_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_831_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_831_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_831_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v_start_824_; lean_object* v_stop_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_823_ = l_Array_toSubarray___redArg(v_x_786_, v_lower_812_, v_upper_813_);
v_start_824_ = lean_ctor_get(v___x_823_, 1);
lean_inc(v_start_824_);
v_stop_825_ = lean_ctor_get(v___x_823_, 2);
lean_inc(v_stop_825_);
lean_dec_ref(v___x_823_);
v___x_826_ = lean_nat_sub(v_stop_825_, v_start_824_);
lean_dec(v_start_824_);
lean_dec(v_stop_825_);
v___x_827_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_827_, 0, v_elimExpr_782_);
lean_ctor_set(v___x_827_, 1, v_a_781_);
lean_ctor_set(v___x_827_, 2, v_val_806_);
lean_ctor_set(v___x_827_, 3, v_a_810_);
lean_ctor_set(v___x_827_, 4, v_a_819_);
lean_ctor_set(v___x_827_, 5, v___x_826_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_827_);
v___x_829_ = v___x_821_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_upper_813_);
lean_dec(v_lower_812_);
lean_dec(v_a_810_);
lean_dec(v_val_806_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_elimExpr_782_);
lean_dec_ref(v_a_781_);
v_a_832_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_818_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_818_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_val_806_);
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_baseDeclName_x3f_783_);
lean_dec_ref(v_elimExpr_782_);
lean_dec_ref(v_a_781_);
v_a_840_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_809_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_809_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
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
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec(v___x_805_);
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_baseDeclName_x3f_783_);
lean_dec_ref(v_elimExpr_782_);
v___x_848_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
v___x_849_ = l_Lean_indentExpr(v_a_781_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_850_, v___y_795_, v___y_798_, v___y_794_, v___y_796_);
return v___x_851_;
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_baseDeclName_x3f_783_);
lean_dec_ref(v_elimExpr_782_);
lean_dec_ref(v_a_781_);
v_a_852_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_804_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_804_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_baseDeclName_x3f_783_);
lean_dec_ref(v_elimExpr_782_);
lean_dec_ref(v_a_781_);
v_a_860_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_800_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_800_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___boxed(lean_object* v_xs_900_, lean_object* v_a_901_, lean_object* v_elimExpr_902_, lean_object* v_baseDeclName_x3f_903_, lean_object* v_type_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(v_xs_900_, v_a_901_, v_elimExpr_902_, v_baseDeclName_x3f_903_, v_type_904_, v_x_905_, v_x_906_, v_x_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec_ref(v_xs_900_);
return v_res_913_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0(void){
_start:
{
lean_object* v___x_914_; lean_object* v_dummy_915_; 
v___x_914_ = lean_box(0);
v_dummy_915_ = l_Lean_Expr_sort___override(v___x_914_);
return v_dummy_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0(lean_object* v_a_916_, lean_object* v_elimExpr_917_, lean_object* v_baseDeclName_x3f_918_, lean_object* v_xs_919_, lean_object* v_type_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_dummy_926_; lean_object* v_nargs_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_dummy_926_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___lam__0___closed__0, &l_Lean_Meta_getElimExprInfo___lam__0___closed__0_once, _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0);
v_nargs_927_ = l_Lean_Expr_getAppNumArgs(v_type_920_);
lean_inc(v_nargs_927_);
v___x_928_ = lean_mk_array(v_nargs_927_, v_dummy_926_);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_sub(v_nargs_927_, v___x_929_);
lean_dec(v_nargs_927_);
lean_inc_ref(v_type_920_);
v___x_931_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(v_xs_919_, v_a_916_, v_elimExpr_917_, v_baseDeclName_x3f_918_, v_type_920_, v_type_920_, v___x_928_, v___x_930_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0___boxed(lean_object* v_a_932_, lean_object* v_elimExpr_933_, lean_object* v_baseDeclName_x3f_934_, lean_object* v_xs_935_, lean_object* v_type_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Meta_getElimExprInfo___lam__0(v_a_932_, v_elimExpr_933_, v_baseDeclName_x3f_934_, v_xs_935_, v_type_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec_ref(v_xs_935_);
return v_res_942_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0(void){
_start:
{
lean_object* v___x_943_; double v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_float_of_nat(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(lean_object* v_cls_948_, lean_object* v_msg_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_ref_955_; lean_object* v___x_956_; lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_1001_; 
v_ref_955_ = lean_ctor_get(v___y_952_, 5);
v___x_956_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_1001_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_1001_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v_traceState_962_; lean_object* v_env_963_; lean_object* v_nextMacroScope_964_; lean_object* v_ngen_965_; lean_object* v_auxDeclNGen_966_; lean_object* v_cache_967_; lean_object* v_messages_968_; lean_object* v_infoState_969_; lean_object* v_snapshotTasks_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1000_; 
v___x_961_ = lean_st_ref_take(v___y_953_);
v_traceState_962_ = lean_ctor_get(v___x_961_, 4);
v_env_963_ = lean_ctor_get(v___x_961_, 0);
v_nextMacroScope_964_ = lean_ctor_get(v___x_961_, 1);
v_ngen_965_ = lean_ctor_get(v___x_961_, 2);
v_auxDeclNGen_966_ = lean_ctor_get(v___x_961_, 3);
v_cache_967_ = lean_ctor_get(v___x_961_, 5);
v_messages_968_ = lean_ctor_get(v___x_961_, 6);
v_infoState_969_ = lean_ctor_get(v___x_961_, 7);
v_snapshotTasks_970_ = lean_ctor_get(v___x_961_, 8);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_972_ = v___x_961_;
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_snapshotTasks_970_);
lean_inc(v_infoState_969_);
lean_inc(v_messages_968_);
lean_inc(v_cache_967_);
lean_inc(v_traceState_962_);
lean_inc(v_auxDeclNGen_966_);
lean_inc(v_ngen_965_);
lean_inc(v_nextMacroScope_964_);
lean_inc(v_env_963_);
lean_dec(v___x_961_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
uint64_t v_tid_974_; lean_object* v_traces_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_999_; 
v_tid_974_ = lean_ctor_get_uint64(v_traceState_962_, sizeof(void*)*1);
v_traces_975_ = lean_ctor_get(v_traceState_962_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v_traceState_962_);
if (v_isSharedCheck_999_ == 0)
{
v___x_977_ = v_traceState_962_;
v_isShared_978_ = v_isSharedCheck_999_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_traces_975_);
lean_dec(v_traceState_962_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_999_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; double v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_979_ = lean_box(0);
v___x_980_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0, &l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0);
v___x_981_ = 0;
v___x_982_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1));
v___x_983_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_983_, 0, v_cls_948_);
lean_ctor_set(v___x_983_, 1, v___x_979_);
lean_ctor_set(v___x_983_, 2, v___x_982_);
lean_ctor_set_float(v___x_983_, sizeof(void*)*3, v___x_980_);
lean_ctor_set_float(v___x_983_, sizeof(void*)*3 + 8, v___x_980_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*3 + 16, v___x_981_);
v___x_984_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2));
v___x_985_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v_a_957_);
lean_ctor_set(v___x_985_, 2, v___x_984_);
lean_inc(v_ref_955_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v_ref_955_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_PersistentArray_push___redArg(v_traces_975_, v___x_986_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_987_);
v___x_989_ = v___x_977_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_987_);
lean_ctor_set_uint64(v_reuseFailAlloc_998_, sizeof(void*)*1, v_tid_974_);
v___x_989_ = v_reuseFailAlloc_998_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 4, v___x_989_);
v___x_991_ = v___x_972_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_env_963_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_nextMacroScope_964_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_ngen_965_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_auxDeclNGen_966_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_997_, 5, v_cache_967_);
lean_ctor_set(v_reuseFailAlloc_997_, 6, v_messages_968_);
lean_ctor_set(v_reuseFailAlloc_997_, 7, v_infoState_969_);
lean_ctor_set(v_reuseFailAlloc_997_, 8, v_snapshotTasks_970_);
v___x_991_ = v_reuseFailAlloc_997_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_992_ = lean_st_ref_put(v___y_953_, v___x_991_);
v___x_993_ = lean_box(0);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_993_);
v___x_995_ = v___x_959_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___boxed(lean_object* v_cls_1002_, lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(v_cls_1002_, v_msg_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1009_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__5(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__2));
v___x_1019_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__4));
v___x_1020_ = l_Lean_Name_append(v___x_1019_, v___x_1018_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__7(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__6));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__9(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__8));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo(lean_object* v_elimExpr_1027_, lean_object* v_baseDeclName_x3f_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; 
lean_inc(v_a_1032_);
lean_inc_ref(v_a_1031_);
lean_inc(v_a_1030_);
lean_inc_ref(v_a_1029_);
lean_inc_ref(v_elimExpr_1027_);
v___x_1034_ = lean_infer_type(v_elimExpr_1027_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_options_1035_; lean_object* v_a_1036_; lean_object* v_inheritedTraceOptions_1037_; uint8_t v_hasTrace_1038_; lean_object* v___f_1039_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; 
v_options_1035_ = lean_ctor_get(v_a_1031_, 2);
v_a_1036_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_n(v_a_1036_, 2);
lean_dec_ref_known(v___x_1034_, 1);
v_inheritedTraceOptions_1037_ = lean_ctor_get(v_a_1031_, 13);
v_hasTrace_1038_ = lean_ctor_get_uint8(v_options_1035_, sizeof(void*)*1);
lean_inc_ref(v_elimExpr_1027_);
v___f_1039_ = lean_alloc_closure((void*)(l_Lean_Meta_getElimExprInfo___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1039_, 0, v_a_1036_);
lean_closure_set(v___f_1039_, 1, v_elimExpr_1027_);
lean_closure_set(v___f_1039_, 2, v_baseDeclName_x3f_1028_);
if (v_hasTrace_1038_ == 0)
{
lean_dec_ref(v_elimExpr_1027_);
v___y_1041_ = v_a_1029_;
v___y_1042_ = v_a_1030_;
v___y_1043_ = v_a_1031_;
v___y_1044_ = v_a_1032_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__2));
v___x_1048_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__5, &l_Lean_Meta_getElimExprInfo___closed__5_once, _init_l_Lean_Meta_getElimExprInfo___closed__5);
v___x_1049_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1037_, v_options_1035_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_dec_ref(v_elimExpr_1027_);
v___y_1041_ = v_a_1029_;
v___y_1042_ = v_a_1030_;
v___y_1043_ = v_a_1031_;
v___y_1044_ = v_a_1032_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1050_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__7, &l_Lean_Meta_getElimExprInfo___closed__7_once, _init_l_Lean_Meta_getElimExprInfo___closed__7);
v___x_1051_ = l_Lean_indentExpr(v_elimExpr_1027_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__9, &l_Lean_Meta_getElimExprInfo___closed__9_once, _init_l_Lean_Meta_getElimExprInfo___closed__9);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
lean_inc(v_a_1036_);
v___x_1055_ = l_Lean_indentExpr(v_a_1036_);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(v___x_1047_, v___x_1056_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_dec_ref_known(v___x_1057_, 1);
v___y_1041_ = v_a_1029_;
v___y_1042_ = v_a_1030_;
v___y_1043_ = v_a_1031_;
v___y_1044_ = v_a_1032_;
goto v___jp_1040_;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v___f_1039_);
lean_dec(v_a_1036_);
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
v___jp_1040_:
{
uint8_t v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = 0;
v___x_1046_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_1036_, v___f_1039_, v___x_1045_, v___x_1045_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1046_;
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_baseDeclName_x3f_1028_);
lean_dec_ref(v_elimExpr_1027_);
v_a_1066_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1034_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1034_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___boxed(lean_object* v_elimExpr_1074_, lean_object* v_baseDeclName_x3f_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Meta_getElimExprInfo(v_elimExpr_1074_, v_baseDeclName_x3f_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(lean_object* v_00_u03b1_1082_, lean_object* v_msg_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___boxed(lean_object* v_00_u03b1_1090_, lean_object* v_msg_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(v_00_u03b1_1090_, v_msg_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(lean_object* v_upperBound_1098_, lean_object* v_xs_1099_, lean_object* v_motive_1100_, lean_object* v___x_1101_, lean_object* v_baseDeclName_x3f_1102_, lean_object* v___x_1103_, lean_object* v_inst_1104_, lean_object* v_R_1105_, lean_object* v_a_1106_, lean_object* v_b_1107_, lean_object* v_c_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v_upperBound_1098_, v_xs_1099_, v_motive_1100_, v___x_1101_, v_baseDeclName_x3f_1102_, v___x_1103_, v_a_1106_, v_b_1107_, v___y_1109_, v___y_1111_, v___y_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___boxed(lean_object* v_upperBound_1115_, lean_object* v_xs_1116_, lean_object* v_motive_1117_, lean_object* v___x_1118_, lean_object* v_baseDeclName_x3f_1119_, lean_object* v___x_1120_, lean_object* v_inst_1121_, lean_object* v_R_1122_, lean_object* v_a_1123_, lean_object* v_b_1124_, lean_object* v_c_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(v_upperBound_1115_, v_xs_1116_, v_motive_1117_, v___x_1118_, v_baseDeclName_x3f_1119_, v___x_1120_, v_inst_1121_, v_R_1122_, v_a_1123_, v_b_1124_, v_c_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v___x_1118_);
lean_dec_ref(v_motive_1117_);
lean_dec_ref(v_xs_1116_);
lean_dec(v_upperBound_1115_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object* v_elimName_1132_, lean_object* v_baseDeclName_x3f_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_elimName_1132_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = l_Lean_Meta_getElimExprInfo(v_a_1140_, v_baseDeclName_x3f_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
return v___x_1141_;
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_baseDeclName_x3f_1133_);
v_a_1142_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1139_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___boxed(lean_object* v_elimName_1150_, lean_object* v_baseDeclName_x3f_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Meta_getElimInfo(v_elimName_1150_, v_baseDeclName_x3f_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
return v_res_1157_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(lean_object* v_a_1158_, lean_object* v_as_1159_, size_t v_i_1160_, size_t v_stop_1161_){
_start:
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_usize_dec_eq(v_i_1160_, v_stop_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = lean_array_uget_borrowed(v_as_1159_, v_i_1160_);
v___x_1164_ = lean_nat_dec_eq(v_a_1158_, v___x_1163_);
if (v___x_1164_ == 0)
{
size_t v___x_1165_; size_t v___x_1166_; 
v___x_1165_ = ((size_t)1ULL);
v___x_1166_ = lean_usize_add(v_i_1160_, v___x_1165_);
v_i_1160_ = v___x_1166_;
goto _start;
}
else
{
return v___x_1164_;
}
}
else
{
uint8_t v___x_1168_; 
v___x_1168_ = 0;
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0___boxed(lean_object* v_a_1169_, lean_object* v_as_1170_, lean_object* v_i_1171_, lean_object* v_stop_1172_){
_start:
{
size_t v_i_boxed_1173_; size_t v_stop_boxed_1174_; uint8_t v_res_1175_; lean_object* v_r_1176_; 
v_i_boxed_1173_ = lean_unbox_usize(v_i_1171_);
lean_dec(v_i_1171_);
v_stop_boxed_1174_ = lean_unbox_usize(v_stop_1172_);
lean_dec(v_stop_1172_);
v_res_1175_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_1169_, v_as_1170_, v_i_boxed_1173_, v_stop_boxed_1174_);
lean_dec_ref(v_as_1170_);
lean_dec(v_a_1169_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(lean_object* v_as_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_array_get_size(v_as_1177_);
v___x_1181_ = lean_nat_dec_lt(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
return v___x_1181_;
}
else
{
if (v___x_1181_ == 0)
{
return v___x_1181_;
}
else
{
size_t v___x_1182_; size_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = lean_usize_of_nat(v___x_1180_);
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_1178_, v_as_1177_, v___x_1182_, v___x_1183_);
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0___boxed(lean_object* v_as_1185_, lean_object* v_a_1186_){
_start:
{
uint8_t v_res_1187_; lean_object* v_r_1188_; 
v_res_1187_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_as_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_as_1185_);
v_r_1188_ = lean_box(v_res_1187_);
return v_r_1188_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1));
v___x_1193_ = l_Lean_stringToMessageData(v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3));
v___x_1196_ = l_Lean_stringToMessageData(v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5));
v___x_1199_ = l_Lean_stringToMessageData(v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7));
v___x_1202_ = l_Lean_stringToMessageData(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9));
v___x_1205_ = l_Lean_stringToMessageData(v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(lean_object* v_elimInfo_1206_, lean_object* v_targets_1207_, lean_object* v_type_1208_, lean_object* v_argIdx_1209_, lean_object* v_targetIdx_1210_, lean_object* v_implicits_1211_, lean_object* v_targets_x27_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Meta_whnfD(v_type_1208_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
if (lean_obj_tag(v_a_1222_) == 7)
{
lean_object* v_binderName_1223_; lean_object* v_binderType_1224_; lean_object* v_body_1225_; uint8_t v_binderInfo_1226_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v_elimExpr_1294_; lean_object* v_targetsPos_1295_; uint8_t v___x_1296_; 
v_binderName_1223_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_binderName_1223_);
v_binderType_1224_ = lean_ctor_get(v_a_1222_, 1);
lean_inc_ref(v_binderType_1224_);
v_body_1225_ = lean_ctor_get(v_a_1222_, 2);
lean_inc_ref(v_body_1225_);
v_binderInfo_1226_ = lean_ctor_get_uint8(v_a_1222_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1222_, 3);
v_elimExpr_1294_ = lean_ctor_get(v_elimInfo_1206_, 0);
v_targetsPos_1295_ = lean_ctor_get(v_elimInfo_1206_, 3);
v___x_1296_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_targetsPos_1295_, v_argIdx_1209_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec(v_binderName_1223_);
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v_binderType_1224_);
v___x_1298_ = 0;
v___x_1299_ = lean_box(0);
v___x_1300_ = l_Lean_Meta_mkFreshExprMVar(v___x_1297_, v___x_1298_, v___x_1299_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = lean_expr_instantiate1(v_body_1225_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_body_1225_);
v___x_1303_ = lean_unsigned_to_nat(1u);
v___x_1304_ = lean_nat_add(v_argIdx_1209_, v___x_1303_);
lean_dec(v_argIdx_1209_);
v_type_1208_ = v___x_1302_;
v_argIdx_1209_ = v___x_1304_;
goto _start;
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1306_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1300_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1300_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
uint8_t v___x_1314_; 
v___x_1314_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1226_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_binderType_1224_);
v___x_1316_ = 0;
v___x_1317_ = l_Lean_Meta_mkFreshExprMVar(v___x_1315_, v___x_1316_, v_binderName_1223_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = lean_expr_instantiate1(v_body_1225_, v_a_1318_);
lean_dec_ref(v_body_1225_);
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v_argIdx_1209_, v___x_1320_);
lean_dec(v_argIdx_1209_);
v___x_1322_ = l_Lean_Expr_mvarId_x21(v_a_1318_);
v___x_1323_ = lean_array_push(v_implicits_1211_, v___x_1322_);
v___x_1324_ = lean_array_push(v_targets_x27_1212_, v_a_1318_);
v_type_1208_ = v___x_1319_;
v_argIdx_1209_ = v___x_1321_;
v_implicits_1211_ = v___x_1323_;
v_targets_x27_1212_ = v___x_1324_;
goto _start;
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1326_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1317_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1317_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
lean_dec(v_binderName_1223_);
v___x_1334_ = lean_array_get_size(v_targets_1207_);
v___x_1335_ = lean_nat_dec_lt(v_targetIdx_1210_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1336_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6);
lean_inc_ref(v_elimExpr_1294_);
v___x_1337_ = l_Lean_MessageData_ofExpr(v_elimExpr_1294_);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1340_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref_known(v___x_1341_, 1);
v___y_1240_ = v_a_1213_;
v___y_1241_ = v_a_1214_;
v___y_1242_ = v_a_1215_;
v___y_1243_ = v_a_1216_;
goto v___jp_1239_;
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_binderType_1224_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
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
else
{
v___y_1240_ = v_a_1213_;
v___y_1241_ = v_a_1214_;
v___y_1242_ = v_a_1215_;
v___y_1243_ = v_a_1216_;
goto v___jp_1239_;
}
}
}
v___jp_1227_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1233_ = lean_expr_instantiate1(v_body_1225_, v___y_1228_);
lean_dec_ref(v_body_1225_);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v_argIdx_1209_, v___x_1234_);
lean_dec(v_argIdx_1209_);
v___x_1236_ = lean_nat_add(v_targetIdx_1210_, v___x_1234_);
lean_dec(v_targetIdx_1210_);
v___x_1237_ = lean_array_push(v_targets_x27_1212_, v___y_1228_);
v_type_1208_ = v___x_1233_;
v_argIdx_1209_ = v___x_1235_;
v_targetIdx_1210_ = v___x_1236_;
v_targets_x27_1212_ = v___x_1237_;
v_a_1213_ = v___y_1229_;
v_a_1214_ = v___y_1230_;
v_a_1215_ = v___y_1231_;
v_a_1216_ = v___y_1232_;
goto _start;
}
v___jp_1239_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = l_Lean_instInhabitedExpr;
v___x_1245_ = lean_array_get_borrowed(v___x_1244_, v_targets_1207_, v_targetIdx_1210_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___x_1245_);
v___x_1246_ = lean_infer_type(v___x_1245_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc_n(v_a_1247_, 2);
lean_dec_ref_known(v___x_1246_, 1);
lean_inc_ref(v_binderType_1224_);
v___x_1248_ = l_Lean_Meta_isExprDefEq(v_binderType_1224_, v_a_1247_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; uint8_t v___x_1250_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1250_ = lean_unbox(v_a_1249_);
lean_dec(v_a_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0));
v___x_1253_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_1247_, v_binderType_1224_, v___x_1251_, v___x_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2);
lean_inc(v___x_1245_);
v___x_1256_ = l_Lean_indentExpr(v___x_1245_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v_a_1254_);
v___x_1261_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1260_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_dec_ref_known(v___x_1261_, 1);
lean_inc(v___x_1245_);
v___y_1228_ = v___x_1245_;
v___y_1229_ = v___y_1240_;
v___y_1230_ = v___y_1241_;
v___y_1231_ = v___y_1242_;
v___y_1232_ = v___y_1243_;
goto v___jp_1227_;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1270_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1253_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1253_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
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
lean_dec(v_a_1247_);
lean_dec_ref(v_binderType_1224_);
lean_inc(v___x_1245_);
v___y_1228_ = v___x_1245_;
v___y_1229_ = v___y_1240_;
v___y_1230_ = v___y_1241_;
v___y_1231_ = v___y_1242_;
v___y_1232_ = v___y_1243_;
goto v___jp_1227_;
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_a_1247_);
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_binderType_1224_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1278_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1248_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1248_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_binderType_1224_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1286_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1246_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1246_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
else
{
lean_object* v___x_1350_; uint8_t v___x_1351_; 
lean_dec(v_a_1222_);
lean_dec(v_argIdx_1209_);
v___x_1350_ = lean_array_get_size(v_targets_1207_);
v___x_1351_ = lean_nat_dec_eq(v_targetIdx_1210_, v___x_1350_);
lean_dec(v_targetIdx_1210_);
if (v___x_1351_ == 0)
{
lean_object* v_elimExpr_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v_elimExpr_1352_ = lean_ctor_get(v_elimInfo_1206_, 0);
lean_inc_ref(v_elimExpr_1352_);
lean_dec_ref(v_elimInfo_1206_);
v___x_1353_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10);
v___x_1354_ = l_Lean_MessageData_ofExpr(v_elimExpr_1352_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1357_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_dec_ref_known(v___x_1358_, 1);
goto v___jp_1218_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
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
else
{
lean_dec_ref(v_elimInfo_1206_);
goto v___jp_1218_;
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1367_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1221_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1221_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
v___jp_1218_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_implicits_1211_);
lean_ctor_set(v___x_1219_, 1, v_targets_x27_1212_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___boxed(lean_object* v_elimInfo_1375_, lean_object* v_targets_1376_, lean_object* v_type_1377_, lean_object* v_argIdx_1378_, lean_object* v_targetIdx_1379_, lean_object* v_implicits_1380_, lean_object* v_targets_x27_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(v_elimInfo_1375_, v_targets_1376_, v_type_1377_, v_argIdx_1378_, v_targetIdx_1379_, v_implicits_1380_, v_targets_x27_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec_ref(v_targets_1376_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(lean_object* v_e_1388_, lean_object* v___y_1389_){
_start:
{
uint8_t v___x_1391_; 
v___x_1391_ = l_Lean_Expr_hasMVar(v_e_1388_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_e_1388_);
return v___x_1392_;
}
else
{
lean_object* v___x_1393_; lean_object* v_mctx_1394_; lean_object* v___x_1395_; lean_object* v_fst_1396_; lean_object* v_snd_1397_; lean_object* v___x_1398_; lean_object* v_cache_1399_; lean_object* v_zetaDeltaFVarIds_1400_; lean_object* v_postponed_1401_; lean_object* v_diag_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1411_; 
v___x_1393_ = lean_st_ref_get(v___y_1389_);
v_mctx_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc_ref(v_mctx_1394_);
lean_dec(v___x_1393_);
v___x_1395_ = l_Lean_instantiateMVarsCore(v_mctx_1394_, v_e_1388_);
v_fst_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_fst_1396_);
v_snd_1397_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_snd_1397_);
lean_dec_ref(v___x_1395_);
v___x_1398_ = lean_st_ref_take(v___y_1389_);
v_cache_1399_ = lean_ctor_get(v___x_1398_, 1);
v_zetaDeltaFVarIds_1400_ = lean_ctor_get(v___x_1398_, 2);
v_postponed_1401_ = lean_ctor_get(v___x_1398_, 3);
v_diag_1402_ = lean_ctor_get(v___x_1398_, 4);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1398_, 0);
lean_dec(v_unused_1412_);
v___x_1404_ = v___x_1398_;
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_diag_1402_);
lean_inc(v_postponed_1401_);
lean_inc(v_zetaDeltaFVarIds_1400_);
lean_inc(v_cache_1399_);
lean_dec(v___x_1398_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_snd_1397_);
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_snd_1397_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_cache_1399_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_zetaDeltaFVarIds_1400_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_postponed_1401_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_diag_1402_);
v___x_1407_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_st_ref_put(v___y_1389_, v___x_1407_);
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_fst_1396_);
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg___boxed(lean_object* v_e_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_e_1413_, v___y_1414_);
lean_dec(v___y_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(lean_object* v_e_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_e_1417_, v___y_1419_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___boxed(lean_object* v_e_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(v_e_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1430_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1431_, lean_object* v_i_1432_, lean_object* v_k_1433_){
_start:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = lean_array_get_size(v_keys_1431_);
v___x_1435_ = lean_nat_dec_lt(v_i_1432_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_dec(v_i_1432_);
return v___x_1435_;
}
else
{
lean_object* v_k_x27_1436_; uint8_t v___x_1437_; 
v_k_x27_1436_ = lean_array_fget_borrowed(v_keys_1431_, v_i_1432_);
v___x_1437_ = l_Lean_instBEqMVarId_beq(v_k_1433_, v_k_x27_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = lean_nat_add(v_i_1432_, v___x_1438_);
lean_dec(v_i_1432_);
v_i_1432_ = v___x_1439_;
goto _start;
}
else
{
lean_dec(v_i_1432_);
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1441_, lean_object* v_i_1442_, lean_object* v_k_1443_){
_start:
{
uint8_t v_res_1444_; lean_object* v_r_1445_; 
v_res_1444_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1441_, v_i_1442_, v_k_1443_);
lean_dec(v_k_1443_);
lean_dec_ref(v_keys_1441_);
v_r_1445_ = lean_box(v_res_1444_);
return v_r_1445_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1446_, size_t v_x_1447_, lean_object* v_x_1448_){
_start:
{
if (lean_obj_tag(v_x_1446_) == 0)
{
lean_object* v_es_1449_; lean_object* v___x_1450_; size_t v___x_1451_; size_t v___x_1452_; lean_object* v_j_1453_; lean_object* v___x_1454_; 
v_es_1449_ = lean_ctor_get(v_x_1446_, 0);
v___x_1450_ = lean_box(2);
v___x_1451_ = ((size_t)31ULL);
v___x_1452_ = lean_usize_land(v_x_1447_, v___x_1451_);
v_j_1453_ = lean_usize_to_nat(v___x_1452_);
v___x_1454_ = lean_array_get_borrowed(v___x_1450_, v_es_1449_, v_j_1453_);
lean_dec(v_j_1453_);
switch(lean_obj_tag(v___x_1454_))
{
case 0:
{
lean_object* v_key_1455_; uint8_t v___x_1456_; 
v_key_1455_ = lean_ctor_get(v___x_1454_, 0);
v___x_1456_ = l_Lean_instBEqMVarId_beq(v_x_1448_, v_key_1455_);
return v___x_1456_;
}
case 1:
{
lean_object* v_node_1457_; size_t v___x_1458_; size_t v___x_1459_; 
v_node_1457_ = lean_ctor_get(v___x_1454_, 0);
v___x_1458_ = ((size_t)5ULL);
v___x_1459_ = lean_usize_shift_right(v_x_1447_, v___x_1458_);
v_x_1446_ = v_node_1457_;
v_x_1447_ = v___x_1459_;
goto _start;
}
default: 
{
uint8_t v___x_1461_; 
v___x_1461_ = 0;
return v___x_1461_;
}
}
}
else
{
lean_object* v_ks_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_ks_1462_ = lean_ctor_get(v_x_1446_, 0);
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1462_, v___x_1463_, v_x_1448_);
return v___x_1464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
size_t v_x_3335__boxed_1468_; uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_x_3335__boxed_1468_ = lean_unbox_usize(v_x_1466_);
lean_dec(v_x_1466_);
v_res_1469_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1465_, v_x_3335__boxed_1468_, v_x_1467_);
lean_dec(v_x_1467_);
lean_dec_ref(v_x_1465_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(lean_object* v_x_1471_, lean_object* v_x_1472_){
_start:
{
uint64_t v___x_1473_; size_t v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = l_Lean_instHashableMVarId_hash(v_x_1472_);
v___x_1474_ = lean_uint64_to_usize(v___x_1473_);
v___x_1475_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1471_, v___x_1474_, v_x_1472_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg___boxed(lean_object* v_x_1476_, lean_object* v_x_1477_){
_start:
{
uint8_t v_res_1478_; lean_object* v_r_1479_; 
v_res_1478_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_1476_, v_x_1477_);
lean_dec(v_x_1477_);
lean_dec_ref(v_x_1476_);
v_r_1479_ = lean_box(v_res_1478_);
return v_r_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(lean_object* v_mvarId_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v_mctx_1484_; lean_object* v_eAssignment_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = lean_st_ref_get(v___y_1481_);
v_mctx_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc_ref(v_mctx_1484_);
lean_dec(v___x_1483_);
v_eAssignment_1485_ = lean_ctor_get(v_mctx_1484_, 8);
lean_inc_ref(v_eAssignment_1485_);
lean_dec_ref(v_mctx_1484_);
v___x_1486_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_eAssignment_1485_, v_mvarId_1480_);
lean_dec_ref(v_eAssignment_1485_);
v___x_1487_ = lean_box(v___x_1486_);
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg___boxed(lean_object* v_mvarId_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_mvarId_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec(v_mvarId_1489_);
return v_res_1492_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2));
v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(lean_object* v_as_1499_, size_t v_sz_1500_, size_t v_i_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_a_1509_; uint8_t v___x_1513_; 
v___x_1513_ = lean_usize_dec_lt(v_i_1501_, v_sz_1500_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_b_1502_);
return v___x_1514_;
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1516_; 
v_a_1515_ = lean_array_uget_borrowed(v_as_1499_, v_i_1501_);
v___x_1516_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_a_1515_, v___y_1504_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_unbox(v_a_1517_);
lean_dec(v_a_1517_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
lean_inc(v_a_1515_);
v___x_1520_ = l_Lean_MVarId_getDecl(v_a_1515_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_userName_1525_; uint8_t v___x_1526_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v_userName_1525_ = lean_ctor_get(v_a_1521_, 0);
lean_inc(v_userName_1525_);
lean_dec(v_a_1521_);
v___x_1526_ = l_Lean_Name_isAnonymous(v_userName_1525_);
if (v___x_1526_ == 0)
{
uint8_t v___x_1527_; 
v___x_1527_ = l_Lean_Name_hasMacroScopes(v_userName_1525_);
lean_dec(v_userName_1525_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_inc(v_a_1515_);
v___x_1528_ = l_Lean_MVarId_getDecl(v_a_1515_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v_userName_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v_userName_1530_ = lean_ctor_get(v_a_1529_, 0);
lean_inc(v_userName_1530_);
lean_dec(v_a_1529_);
v___x_1531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3);
v___x_1532_ = l_Lean_MessageData_ofName(v_userName_1530_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1535_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_dec_ref_known(v___x_1536_, 1);
v_a_1509_ = v___x_1518_;
goto v___jp_1508_;
}
else
{
return v___x_1536_;
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_a_1537_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1528_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1528_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
goto v___jp_1522_;
}
}
else
{
lean_dec(v_userName_1525_);
goto v___jp_1522_;
}
v___jp_1522_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1);
v___x_1524_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1523_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_dec_ref_known(v___x_1524_, 1);
v_a_1509_ = v___x_1518_;
goto v___jp_1508_;
}
else
{
return v___x_1524_;
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
v_a_1545_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1520_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1520_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
v_a_1509_ = v___x_1518_;
goto v___jp_1508_;
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
v_a_1553_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1516_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1516_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
v___jp_1508_:
{
size_t v___x_1510_; size_t v___x_1511_; 
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1501_, v___x_1510_);
v_i_1501_ = v___x_1511_;
v_b_1502_ = v_a_1509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___boxed(lean_object* v_as_1561_, lean_object* v_sz_1562_, lean_object* v_i_1563_, lean_object* v_b_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
size_t v_sz_boxed_1570_; size_t v_i_boxed_1571_; lean_object* v_res_1572_; 
v_sz_boxed_1570_ = lean_unbox_usize(v_sz_1562_);
lean_dec(v_sz_1562_);
v_i_boxed_1571_ = lean_unbox_usize(v_i_1563_);
lean_dec(v_i_1563_);
v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_as_1561_, v_sz_boxed_1570_, v_i_boxed_1571_, v_b_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec_ref(v_as_1561_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(size_t v_sz_1573_, size_t v_i_1574_, lean_object* v_bs_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_usize_dec_lt(v_i_1574_, v_sz_1573_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_bs_1575_);
return v___x_1582_;
}
else
{
lean_object* v_v_1583_; lean_object* v___x_1584_; 
v_v_1583_ = lean_array_uget_borrowed(v_bs_1575_, v_i_1574_);
lean_inc(v_v_1583_);
v___x_1584_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_v_1583_, v___y_1577_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v_bs_x27_1587_; size_t v___x_1588_; size_t v___x_1589_; lean_object* v___x_1590_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = lean_unsigned_to_nat(0u);
v_bs_x27_1587_ = lean_array_uset(v_bs_1575_, v_i_1574_, v___x_1586_);
v___x_1588_ = ((size_t)1ULL);
v___x_1589_ = lean_usize_add(v_i_1574_, v___x_1588_);
v___x_1590_ = lean_array_uset(v_bs_x27_1587_, v_i_1574_, v_a_1585_);
v_i_1574_ = v___x_1589_;
v_bs_1575_ = v___x_1590_;
goto _start;
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_bs_1575_);
v_a_1592_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1584_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1584_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3___boxed(lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_bs_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
size_t v_sz_boxed_1608_; size_t v_i_boxed_1609_; lean_object* v_res_1610_; 
v_sz_boxed_1608_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1609_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_boxed_1608_, v_i_boxed_1609_, v_bs_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object* v_elimInfo_1613_, lean_object* v_targets_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_elimType_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_elimType_1620_ = lean_ctor_get(v_elimInfo_1613_, 1);
lean_inc_ref(v_elimType_1620_);
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = ((lean_object*)(l_Lean_Meta_addImplicitTargets___closed__0));
v___x_1623_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(v_elimInfo_1613_, v_targets_1614_, v_elimType_1620_, v___x_1621_, v___x_1621_, v___x_1622_, v___x_1622_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v_fst_1625_; lean_object* v_snd_1626_; lean_object* v___x_1627_; size_t v_sz_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v_fst_1625_ = lean_ctor_get(v_a_1624_, 0);
lean_inc(v_fst_1625_);
v_snd_1626_ = lean_ctor_get(v_a_1624_, 1);
lean_inc(v_snd_1626_);
lean_dec(v_a_1624_);
v___x_1627_ = lean_box(0);
v_sz_1628_ = lean_array_size(v_fst_1625_);
v___x_1629_ = ((size_t)0ULL);
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_fst_1625_, v_sz_1628_, v___x_1629_, v___x_1627_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_fst_1625_);
if (lean_obj_tag(v___x_1630_) == 0)
{
size_t v_sz_1631_; lean_object* v___x_1632_; 
lean_dec_ref_known(v___x_1630_, 1);
v_sz_1631_ = lean_array_size(v_snd_1626_);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_1631_, v___x_1629_, v_snd_1626_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
return v___x_1632_;
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_snd_1626_);
v_a_1633_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1630_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1630_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v_a_1641_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1623_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1623_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___boxed(lean_object* v_elimInfo_1649_, lean_object* v_targets_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Meta_addImplicitTargets(v_elimInfo_1649_, v_targets_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec_ref(v_targets_1650_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(lean_object* v_mvarId_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_mvarId_1657_, v___y_1659_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___boxed(lean_object* v_mvarId_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(v_mvarId_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v_mvarId_1664_);
return v_res_1670_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(lean_object* v_00_u03b2_1671_, lean_object* v_x_1672_, lean_object* v_x_1673_){
_start:
{
uint8_t v___x_1674_; 
v___x_1674_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_1672_, v_x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
uint8_t v_res_1678_; lean_object* v_r_1679_; 
v_res_1678_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(v_00_u03b2_1675_, v_x_1676_, v_x_1677_);
lean_dec(v_x_1677_);
lean_dec_ref(v_x_1676_);
v_r_1679_ = lean_box(v_res_1678_);
return v_r_1679_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1680_, lean_object* v_x_1681_, size_t v_x_1682_, lean_object* v_x_1683_){
_start:
{
uint8_t v___x_1684_; 
v___x_1684_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1681_, v_x_1682_, v_x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_, lean_object* v_x_1688_){
_start:
{
size_t v_x_3678__boxed_1689_; uint8_t v_res_1690_; lean_object* v_r_1691_; 
v_x_3678__boxed_1689_ = lean_unbox_usize(v_x_1687_);
lean_dec(v_x_1687_);
v_res_1690_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(v_00_u03b2_1685_, v_x_1686_, v_x_3678__boxed_1689_, v_x_1688_);
lean_dec(v_x_1688_);
lean_dec_ref(v_x_1686_);
v_r_1691_ = lean_box(v_res_1690_);
return v_r_1691_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1692_, lean_object* v_keys_1693_, lean_object* v_vals_1694_, lean_object* v_heq_1695_, lean_object* v_i_1696_, lean_object* v_k_1697_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1693_, v_i_1696_, v_k_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1699_, lean_object* v_keys_1700_, lean_object* v_vals_1701_, lean_object* v_heq_1702_, lean_object* v_i_1703_, lean_object* v_k_1704_){
_start:
{
uint8_t v_res_1705_; lean_object* v_r_1706_; 
v_res_1705_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1699_, v_keys_1700_, v_vals_1701_, v_heq_1702_, v_i_1703_, v_k_1704_);
lean_dec(v_k_1704_);
lean_dec_ref(v_vals_1701_);
lean_dec_ref(v_keys_1700_);
v_r_1706_ = lean_box(v_res_1705_);
return v_r_1706_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1717_) == 0)
{
lean_dec(v_x_1715_);
return v_x_1716_;
}
else
{
lean_object* v_head_1718_; lean_object* v_tail_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1730_; 
v_head_1718_ = lean_ctor_get(v_x_1717_, 0);
v_tail_1719_ = lean_ctor_get(v_x_1717_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_x_1717_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1721_ = v_x_1717_;
v_isShared_1722_ = v_isSharedCheck_1730_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_tail_1719_);
lean_inc(v_head_1718_);
lean_dec(v_x_1717_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1730_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
lean_inc(v_x_1715_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set_tag(v___x_1721_, 5);
lean_ctor_set(v___x_1721_, 1, v_x_1715_);
lean_ctor_set(v___x_1721_, 0, v_x_1716_);
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_x_1716_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_x_1715_);
v___x_1724_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = l_Lean_Name_reprPrec(v_head_1718_, v___x_1725_);
v___x_1727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1724_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v_x_1716_ = v___x_1727_;
v_x_1717_ = v_tail_1719_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
if (lean_obj_tag(v_x_1733_) == 0)
{
lean_dec(v_x_1731_);
return v_x_1732_;
}
else
{
lean_object* v_head_1734_; lean_object* v_tail_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1746_; 
v_head_1734_ = lean_ctor_get(v_x_1733_, 0);
v_tail_1735_ = lean_ctor_get(v_x_1733_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_x_1733_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1737_ = v_x_1733_;
v_isShared_1738_ = v_isSharedCheck_1746_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_tail_1735_);
lean_inc(v_head_1734_);
lean_dec(v_x_1733_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1746_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
lean_inc(v_x_1731_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 5);
lean_ctor_set(v___x_1737_, 1, v_x_1731_);
lean_ctor_set(v___x_1737_, 0, v_x_1732_);
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_x_1732_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_x_1731_);
v___x_1740_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = l_Lean_Name_reprPrec(v_head_1734_, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1740_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(v_x_1731_, v___x_1743_, v_tail_1735_);
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = l_Lean_Name_reprPrec(v___y_1747_, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
if (lean_obj_tag(v_x_1750_) == 0)
{
lean_object* v___x_1752_; 
lean_dec(v_x_1751_);
v___x_1752_ = lean_box(0);
return v___x_1752_;
}
else
{
lean_object* v_tail_1753_; 
v_tail_1753_ = lean_ctor_get(v_x_1750_, 1);
if (lean_obj_tag(v_tail_1753_) == 0)
{
lean_object* v_head_1754_; lean_object* v___x_1755_; 
lean_dec(v_x_1751_);
v_head_1754_ = lean_ctor_get(v_x_1750_, 0);
lean_inc(v_head_1754_);
lean_dec_ref_known(v_x_1750_, 2);
v___x_1755_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_1754_);
return v___x_1755_;
}
else
{
lean_object* v_head_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_inc(v_tail_1753_);
v_head_1756_ = lean_ctor_get(v_x_1750_, 0);
lean_inc(v_head_1756_);
lean_dec_ref_known(v_x_1750_, 2);
v___x_1757_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_1756_);
v___x_1758_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(v_x_1751_, v___x_1757_, v_tail_1753_);
return v___x_1758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(lean_object* v_xs_1759_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1760_ = lean_array_get_size(v_xs_1759_);
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = lean_nat_dec_eq(v___x_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1763_ = lean_array_to_list(v_xs_1759_);
v___x_1764_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_1765_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(v___x_1763_, v___x_1764_);
v___x_1766_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4);
v___x_1767_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5));
v___x_1768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___x_1765_);
v___x_1769_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_1770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1766_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = l_Std_Format_fill(v___x_1771_);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; 
lean_dec_ref(v_xs_1759_);
v___x_1773_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8));
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg(lean_object* v_x_1788_){
_start:
{
uint8_t v_induction_1789_; lean_object* v_typeNames_1790_; lean_object* v_elimName_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_induction_1789_ = lean_ctor_get_uint8(v_x_1788_, sizeof(void*)*2);
v_typeNames_1790_ = lean_ctor_get(v_x_1788_, 0);
lean_inc_ref(v_typeNames_1790_);
v_elimName_1791_ = lean_ctor_get(v_x_1788_, 1);
lean_inc(v_elimName_1791_);
lean_dec_ref(v_x_1788_);
v___x_1792_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5));
v___x_1793_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2));
v___x_1794_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = l_Bool_repr___redArg(v_induction_1789_);
v___x_1797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1794_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = 0;
v___x_1799_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*1, v___x_1798_);
v___x_1800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1793_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9));
v___x_1802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = lean_box(1);
v___x_1804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4));
v___x_1806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v___x_1792_);
v___x_1808_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_typeNames_1790_);
v___x_1809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1794_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*1, v___x_1798_);
v___x_1811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1807_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set(v___x_1812_, 1, v___x_1801_);
v___x_1813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1803_);
v___x_1814_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6));
v___x_1815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v___x_1792_);
v___x_1817_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4);
v___x_1818_ = l_Lean_Name_reprPrec(v_elimName_1791_, v___x_1795_);
v___x_1819_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*1, v___x_1798_);
v___x_1821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1816_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_1823_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_1824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v___x_1821_);
v___x_1825_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_1826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1822_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set_uint8(v___x_1828_, sizeof(void*)*1, v___x_1798_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr(lean_object* v_x_1829_, lean_object* v_prec_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_Meta_instReprCustomEliminator_repr___redArg(v_x_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___boxed(lean_object* v_x_1832_, lean_object* v_prec_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Meta_instReprCustomEliminator_repr(v_x_1832_, v_prec_1833_);
lean_dec(v_prec_1833_);
return v_res_1834_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0(void){
_start:
{
lean_object* v_cellCount_1837_; lean_object* v___x_1838_; 
v_cellCount_1837_ = lean_unsigned_to_nat(16u);
v___x_1838_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1837_);
return v___x_1838_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1(void){
_start:
{
lean_object* v_cellCount_1839_; lean_object* v___x_1840_; 
v_cellCount_1839_ = lean_unsigned_to_nat(16u);
v___x_1840_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1841_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1);
v___x_1842_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0);
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v___x_1842_);
lean_ctor_set(v___x_1844_, 2, v___x_1841_);
return v___x_1844_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3(void){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__5(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; 
v___x_1848_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4);
v___x_1849_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2);
v___x_1850_ = 1;
v___x_1851_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1848_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*2, v___x_1850_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default(void){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__5, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__5_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__5);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators(void){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0(lean_object* v_f_1854_, lean_object* v_x1_1855_, lean_object* v_x2_1856_, lean_object* v_x3_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_apply_3(v_f_1854_, v_x1_1855_, v_x2_1856_, v_x3_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13___redArg(lean_object* v_f_1859_, lean_object* v_keys_1860_, lean_object* v_vals_1861_, lean_object* v_i_1862_, lean_object* v_acc_1863_){
_start:
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = lean_array_get_size(v_keys_1860_);
v___x_1865_ = lean_nat_dec_lt(v_i_1862_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_dec(v_i_1862_);
lean_dec(v_f_1859_);
return v_acc_1863_;
}
else
{
lean_object* v_k_1866_; lean_object* v_v_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_k_1866_ = lean_array_fget_borrowed(v_keys_1860_, v_i_1862_);
v_v_1867_ = lean_array_fget_borrowed(v_vals_1861_, v_i_1862_);
lean_inc(v_f_1859_);
lean_inc(v_v_1867_);
lean_inc(v_k_1866_);
v___x_1868_ = lean_apply_3(v_f_1859_, v_acc_1863_, v_k_1866_, v_v_1867_);
v___x_1869_ = lean_unsigned_to_nat(1u);
v___x_1870_ = lean_nat_add(v_i_1862_, v___x_1869_);
lean_dec(v_i_1862_);
v_i_1862_ = v___x_1870_;
v_acc_1863_ = v___x_1868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_f_1872_, lean_object* v_keys_1873_, lean_object* v_vals_1874_, lean_object* v_i_1875_, lean_object* v_acc_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13___redArg(v_f_1872_, v_keys_1873_, v_vals_1874_, v_i_1875_, v_acc_1876_);
lean_dec_ref(v_vals_1874_);
lean_dec_ref(v_keys_1873_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___redArg(lean_object* v_f_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
lean_object* v_es_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v_es_1881_ = lean_ctor_get(v_x_1879_, 0);
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = lean_array_get_size(v_es_1881_);
v___x_1884_ = lean_nat_dec_lt(v___x_1882_, v___x_1883_);
if (v___x_1884_ == 0)
{
lean_dec(v_f_1878_);
return v_x_1880_;
}
else
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_nat_dec_le(v___x_1883_, v___x_1883_);
if (v___x_1885_ == 0)
{
if (v___x_1884_ == 0)
{
lean_dec(v_f_1878_);
return v_x_1880_;
}
else
{
size_t v___x_1886_; size_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = ((size_t)0ULL);
v___x_1887_ = lean_usize_of_nat(v___x_1883_);
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12___redArg(v_f_1878_, v_es_1881_, v___x_1886_, v___x_1887_, v_x_1880_);
return v___x_1888_;
}
}
else
{
size_t v___x_1889_; size_t v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = ((size_t)0ULL);
v___x_1890_ = lean_usize_of_nat(v___x_1883_);
v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12___redArg(v_f_1878_, v_es_1881_, v___x_1889_, v___x_1890_, v_x_1880_);
return v___x_1891_;
}
}
}
else
{
lean_object* v_ks_1892_; lean_object* v_vs_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_ks_1892_ = lean_ctor_get(v_x_1879_, 0);
v_vs_1893_ = lean_ctor_get(v_x_1879_, 1);
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13___redArg(v_f_1878_, v_ks_1892_, v_vs_1893_, v___x_1894_, v_x_1880_);
return v___x_1895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12___redArg(lean_object* v_f_1896_, lean_object* v_as_1897_, size_t v_i_1898_, size_t v_stop_1899_, lean_object* v_b_1900_){
_start:
{
lean_object* v___y_1902_; uint8_t v___x_1906_; 
v___x_1906_ = lean_usize_dec_eq(v_i_1898_, v_stop_1899_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_array_uget_borrowed(v_as_1897_, v_i_1898_);
switch(lean_obj_tag(v___x_1907_))
{
case 0:
{
lean_object* v_key_1908_; lean_object* v_val_1909_; lean_object* v___x_1910_; 
v_key_1908_ = lean_ctor_get(v___x_1907_, 0);
v_val_1909_ = lean_ctor_get(v___x_1907_, 1);
lean_inc(v_f_1896_);
lean_inc(v_val_1909_);
lean_inc(v_key_1908_);
v___x_1910_ = lean_apply_3(v_f_1896_, v_b_1900_, v_key_1908_, v_val_1909_);
v___y_1902_ = v___x_1910_;
goto v___jp_1901_;
}
case 1:
{
lean_object* v_node_1911_; lean_object* v___x_1912_; 
v_node_1911_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_f_1896_);
v___x_1912_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___redArg(v_f_1896_, v_node_1911_, v_b_1900_);
v___y_1902_ = v___x_1912_;
goto v___jp_1901_;
}
default: 
{
v___y_1902_ = v_b_1900_;
goto v___jp_1901_;
}
}
}
else
{
lean_dec(v_f_1896_);
return v_b_1900_;
}
v___jp_1901_:
{
size_t v___x_1903_; size_t v___x_1904_; 
v___x_1903_ = ((size_t)1ULL);
v___x_1904_ = lean_usize_add(v_i_1898_, v___x_1903_);
v_i_1898_ = v___x_1904_;
v_b_1900_ = v___y_1902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_f_1913_, lean_object* v_as_1914_, lean_object* v_i_1915_, lean_object* v_stop_1916_, lean_object* v_b_1917_){
_start:
{
size_t v_i_boxed_1918_; size_t v_stop_boxed_1919_; lean_object* v_res_1920_; 
v_i_boxed_1918_ = lean_unbox_usize(v_i_1915_);
lean_dec(v_i_1915_);
v_stop_boxed_1919_ = lean_unbox_usize(v_stop_1916_);
lean_dec(v_stop_1916_);
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12___redArg(v_f_1913_, v_as_1914_, v_i_boxed_1918_, v_stop_boxed_1919_, v_b_1917_);
lean_dec_ref(v_as_1914_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___redArg(v_f_1921_, v_x_1922_, v_x_1923_);
lean_dec_ref(v_x_1922_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_map_1925_, lean_object* v_f_1926_, lean_object* v_init_1927_){
_start:
{
lean_object* v___f_1928_; lean_object* v___x_1929_; 
v___f_1928_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1928_, 0, v_f_1926_);
v___x_1929_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___redArg(v___f_1928_, v_map_1925_, v_init_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_map_1930_, lean_object* v_f_1931_, lean_object* v_init_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_1930_, v_f_1931_, v_init_1932_);
lean_dec_ref(v_map_1930_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1934_, lean_object* v_b_1935_, lean_object* v_acc_1936_, lean_object* v_i_1937_){
_start:
{
lean_object* v_keyArray_1942_; lean_object* v_valueArray_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v_keyArray_1942_ = lean_ctor_get(v_b_1935_, 1);
v_valueArray_1943_ = lean_ctor_get(v_b_1935_, 2);
v___x_1944_ = lean_array_get_size(v_keyArray_1942_);
v___x_1945_ = lean_nat_dec_lt(v_i_1937_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_dec(v_i_1937_);
lean_dec(v_f_1934_);
return v_acc_1936_;
}
else
{
lean_object* v___x_1946_; uint8_t v_isSome_1947_; 
v___x_1946_ = lean_array_fget_borrowed(v_keyArray_1942_, v_i_1937_);
v_isSome_1947_ = lean_noption_is_some(v___x_1946_);
if (v_isSome_1947_ == 0)
{
goto v___jp_1938_;
}
else
{
lean_object* v___x_1948_; uint8_t v_isSome_1949_; 
v___x_1948_ = lean_array_fget_borrowed(v_valueArray_1943_, v_i_1937_);
v_isSome_1949_ = lean_noption_is_some(v___x_1948_);
if (v_isSome_1949_ == 0)
{
goto v___jp_1938_;
}
else
{
lean_object* v_val_1950_; lean_object* v_val_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_inc(v___x_1946_);
v_val_1950_ = lean_noption_get(v___x_1946_);
lean_inc(v___x_1948_);
v_val_1951_ = lean_noption_get(v___x_1948_);
lean_inc(v_f_1934_);
v___x_1952_ = lean_apply_3(v_f_1934_, v_acc_1936_, v_val_1950_, v_val_1951_);
v___x_1953_ = lean_unsigned_to_nat(1u);
v___x_1954_ = lean_nat_add(v_i_1937_, v___x_1953_);
lean_dec(v_i_1937_);
v_acc_1936_ = v___x_1952_;
v_i_1937_ = v___x_1954_;
goto _start;
}
}
}
v___jp_1938_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_unsigned_to_nat(1u);
v___x_1940_ = lean_nat_add(v_i_1937_, v___x_1939_);
lean_dec(v_i_1937_);
v_i_1937_ = v___x_1940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1956_, lean_object* v_b_1957_, lean_object* v_acc_1958_, lean_object* v_i_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1956_, v_b_1957_, v_acc_1958_, v_i_1959_);
lean_dec_ref(v_b_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1961_, lean_object* v_init_1962_, lean_object* v_b_1963_){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1961_, v_b_1963_, v_init_1962_, v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1966_, lean_object* v_init_1967_, lean_object* v_b_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_1966_, v_init_1967_, v_b_1968_);
lean_dec_ref(v_b_1968_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(lean_object* v_f_1970_, lean_object* v_init_1971_, lean_object* v_m_1972_){
_start:
{
lean_object* v_map_u2081_1973_; lean_object* v_map_u2082_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v_map_u2081_1973_ = lean_ctor_get(v_m_1972_, 0);
v_map_u2082_1974_ = lean_ctor_get(v_m_1972_, 1);
lean_inc(v_f_1970_);
v___x_1975_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_1970_, v_init_1971_, v_map_u2081_1973_);
v___x_1976_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1974_, v_f_1970_, v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg___boxed(lean_object* v_f_1977_, lean_object* v_init_1978_, lean_object* v_m_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_1977_, v_init_1978_, v_m_1979_);
lean_dec_ref(v_m_1979_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0(lean_object* v_es_1981_, lean_object* v_a_1982_, lean_object* v_b_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_a_1982_);
lean_ctor_set(v___x_1984_, 1, v_b_1983_);
v___x_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
lean_ctor_set(v___x_1985_, 1, v_es_1981_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(lean_object* v_m_1987_){
_start:
{
lean_object* v___f_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___f_1988_ = ((lean_object*)(l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0));
v___x_1989_ = lean_box(0);
v___x_1990_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v___f_1988_, v___x_1989_, v_m_1987_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___boxed(lean_object* v_m_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_m_1991_);
lean_dec_ref(v_m_1991_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6_spec__9(lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 0)
{
lean_dec(v_x_1993_);
return v_x_1994_;
}
else
{
lean_object* v_head_1996_; lean_object* v_tail_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2006_; 
v_head_1996_ = lean_ctor_get(v_x_1995_, 0);
v_tail_1997_ = lean_ctor_get(v_x_1995_, 1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_x_1995_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1999_ = v_x_1995_;
v_isShared_2000_ = v_isSharedCheck_2006_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_tail_1997_);
lean_inc(v_head_1996_);
lean_dec(v_x_1995_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2006_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
lean_inc(v_x_1993_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set_tag(v___x_1999_, 5);
lean_ctor_set(v___x_1999_, 1, v_x_1993_);
lean_ctor_set(v___x_1999_, 0, v_x_1994_);
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_x_1994_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_x_1993_);
v___x_2002_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v_head_1996_);
v_x_1994_ = v___x_2003_;
v_x_1995_ = v_tail_1997_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(lean_object* v_x_2007_, lean_object* v_x_2008_){
_start:
{
if (lean_obj_tag(v_x_2007_) == 0)
{
lean_object* v___x_2009_; 
lean_dec(v_x_2008_);
v___x_2009_ = lean_box(0);
return v___x_2009_;
}
else
{
lean_object* v_tail_2010_; 
v_tail_2010_ = lean_ctor_get(v_x_2007_, 1);
if (lean_obj_tag(v_tail_2010_) == 0)
{
lean_object* v_head_2011_; 
lean_dec(v_x_2008_);
v_head_2011_ = lean_ctor_get(v_x_2007_, 0);
lean_inc(v_head_2011_);
lean_dec_ref_known(v_x_2007_, 2);
return v_head_2011_;
}
else
{
lean_object* v_head_2012_; lean_object* v___x_2013_; 
lean_inc(v_tail_2010_);
v_head_2012_ = lean_ctor_get(v_x_2007_, 0);
lean_inc(v_head_2012_);
lean_dec_ref_known(v_x_2007_, 2);
v___x_2013_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6_spec__9(v_x_2008_, v_head_2012_, v_tail_2010_);
return v___x_2013_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2017_ = lean_string_length(v___x_2016_);
return v___x_2017_;
}
}
static lean_object* _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__2, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__2);
v___x_2019_ = lean_nat_to_int(v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg(lean_object* v_x_2024_){
_start:
{
lean_object* v_fst_2025_; lean_object* v_snd_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2049_; 
v_fst_2025_ = lean_ctor_get(v_x_2024_, 0);
v_snd_2026_ = lean_ctor_get(v_x_2024_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_x_2024_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2028_ = v_x_2024_;
v_isShared_2029_ = v_isSharedCheck_2049_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_snd_2026_);
lean_inc(v_fst_2025_);
lean_dec(v_x_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2049_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
uint8_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2030_ = lean_unbox(v_fst_2025_);
lean_dec(v_fst_2025_);
v___x_2031_ = l_Bool_repr___redArg(v___x_2030_);
v___x_2032_ = lean_box(0);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 1);
lean_ctor_set(v___x_2028_, 1, v___x_2032_);
lean_ctor_set(v___x_2028_, 0, v___x_2031_);
v___x_2034_ = v___x_2028_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; 
v___x_2035_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_snd_2026_);
v___x_2036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v___x_2034_);
v___x_2037_ = l_List_reverse___redArg(v___x_2036_);
v___x_2038_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2039_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(v___x_2037_, v___x_2038_);
v___x_2040_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__3, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2041_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__4));
v___x_2042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v___x_2039_);
v___x_2043_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__5));
v___x_2044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2042_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2040_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = 0;
v___x_2047_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*1, v___x_2046_);
return v___x_2047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(lean_object* v_x_2050_){
_start:
{
lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2075_; 
v_fst_2051_ = lean_ctor_get(v_x_2050_, 0);
v_snd_2052_ = lean_ctor_get(v_x_2050_, 1);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_x_2050_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2054_ = v_x_2050_;
v_isShared_2055_ = v_isSharedCheck_2075_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_snd_2052_);
lean_inc(v_fst_2051_);
lean_dec(v_x_2050_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2075_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2057_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg(v_fst_2051_);
v___x_2058_ = lean_box(0);
if (v_isShared_2055_ == 0)
{
lean_ctor_set_tag(v___x_2054_, 1);
lean_ctor_set(v___x_2054_, 1, v___x_2058_);
lean_ctor_set(v___x_2054_, 0, v___x_2057_);
v___x_2060_ = v___x_2054_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2061_ = l_Lean_Name_reprPrec(v_snd_2052_, v___x_2056_);
v___x_2062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v___x_2060_);
v___x_2063_ = l_List_reverse___redArg(v___x_2062_);
v___x_2064_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2065_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(v___x_2063_, v___x_2064_);
v___x_2066_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__3, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2067_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__4));
v___x_2068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v___x_2065_);
v___x_2069_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg___closed__5));
v___x_2070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2068_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2066_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = 0;
v___x_2073_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*1, v___x_2072_);
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__8_spec__12(lean_object* v_x_2076_, lean_object* v_x_2077_, lean_object* v_x_2078_){
_start:
{
if (lean_obj_tag(v_x_2078_) == 0)
{
lean_dec(v_x_2076_);
return v_x_2077_;
}
else
{
lean_object* v_head_2079_; lean_object* v_tail_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2090_; 
v_head_2079_ = lean_ctor_get(v_x_2078_, 0);
v_tail_2080_ = lean_ctor_get(v_x_2078_, 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_x_2078_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2082_ = v_x_2078_;
v_isShared_2083_ = v_isSharedCheck_2090_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_tail_2080_);
lean_inc(v_head_2079_);
lean_dec(v_x_2078_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2090_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
lean_inc(v_x_2076_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 5);
lean_ctor_set(v___x_2082_, 1, v_x_2076_);
lean_ctor_set(v___x_2082_, 0, v_x_2077_);
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_x_2077_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_x_2076_);
v___x_2085_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2079_);
v___x_2087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2085_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v_x_2077_ = v___x_2087_;
v_x_2078_ = v_tail_2080_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__8(lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_dec(v_x_2091_);
return v_x_2092_;
}
else
{
lean_object* v_head_2094_; lean_object* v_tail_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2105_; 
v_head_2094_ = lean_ctor_get(v_x_2093_, 0);
v_tail_2095_ = lean_ctor_get(v_x_2093_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2097_ = v_x_2093_;
v_isShared_2098_ = v_isSharedCheck_2105_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_tail_2095_);
lean_inc(v_head_2094_);
lean_dec(v_x_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2105_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
lean_inc(v_x_2091_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 5);
lean_ctor_set(v___x_2097_, 1, v_x_2091_);
lean_ctor_set(v___x_2097_, 0, v_x_2092_);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_x_2092_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_x_2091_);
v___x_2100_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2094_);
v___x_2102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__8_spec__12(v_x_2091_, v___x_2102_, v_tail_2095_);
return v___x_2103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(lean_object* v_x_2106_, lean_object* v_x_2107_){
_start:
{
if (lean_obj_tag(v_x_2106_) == 0)
{
lean_object* v___x_2108_; 
lean_dec(v_x_2107_);
v___x_2108_ = lean_box(0);
return v___x_2108_;
}
else
{
lean_object* v_tail_2109_; 
v_tail_2109_ = lean_ctor_get(v_x_2106_, 1);
if (lean_obj_tag(v_tail_2109_) == 0)
{
lean_object* v_head_2110_; lean_object* v___x_2111_; 
lean_dec(v_x_2107_);
v_head_2110_ = lean_ctor_get(v_x_2106_, 0);
lean_inc(v_head_2110_);
lean_dec_ref_known(v_x_2106_, 2);
v___x_2111_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2110_);
return v___x_2111_;
}
else
{
lean_object* v_head_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_inc(v_tail_2109_);
v_head_2112_ = lean_ctor_get(v_x_2106_, 0);
lean_inc(v_head_2112_);
lean_dec_ref_known(v_x_2106_, 2);
v___x_2113_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2112_);
v___x_2114_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__8(v_x_2107_, v___x_2113_, v_tail_2109_);
return v___x_2114_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2));
v___x_2120_ = lean_string_length(v___x_2119_);
return v___x_2120_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3, &l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3_once, _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3);
v___x_2122_ = lean_nat_to_int(v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(lean_object* v_a_2125_){
_start:
{
if (lean_obj_tag(v_a_2125_) == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1));
return v___x_2126_;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2127_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2128_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(v_a_2125_, v___x_2127_);
v___x_2129_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4, &l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4);
v___x_2130_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5));
v___x_2131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v___x_2128_);
v___x_2132_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_2133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2129_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = 0;
v___x_2136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*1, v___x_2135_);
return v___x_2136_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_unsigned_to_nat(7u);
v___x_2147_ = lean_nat_to_int(v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg(lean_object* v_x_2151_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2152_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3));
v___x_2153_ = lean_obj_once(&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4, &l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4);
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_x_2151_);
v___x_2156_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v___x_2155_);
v___x_2157_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6));
v___x_2158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Repr_addAppParen(v___x_2158_, v___x_2154_);
v___x_2160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2153_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = 0;
v___x_2162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2152_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_2165_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_2166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___x_2163_);
v___x_2167_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_2168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2164_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*1, v___x_2161_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___boxed(lean_object* v_x_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_2171_);
lean_dec_ref(v_x_2171_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr(lean_object* v_x_2173_, lean_object* v_prec_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_2173_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___boxed(lean_object* v_x_2176_, lean_object* v_prec_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Meta_instReprCustomEliminators_repr(v_x_2176_, v_prec_2177_);
lean_dec(v_prec_2177_);
lean_dec_ref(v_x_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(lean_object* v_00_u03b2_2179_, lean_object* v_m_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_m_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___boxed(lean_object* v_00_u03b2_2182_, lean_object* v_m_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(v_00_u03b2_2182_, v_m_2183_);
lean_dec_ref(v_m_2183_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(lean_object* v_a_2185_, lean_object* v_n_2186_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v_a_2185_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___boxed(lean_object* v_a_2188_, lean_object* v_n_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(v_a_2188_, v_n_2189_);
lean_dec(v_n_2189_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(lean_object* v_00_u03b2_2191_, lean_object* v_00_u03c3_2192_, lean_object* v_f_2193_, lean_object* v_init_2194_, lean_object* v_m_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_2193_, v_init_2194_, v_m_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2197_, lean_object* v_00_u03c3_2198_, lean_object* v_f_2199_, lean_object* v_init_2200_, lean_object* v_m_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(v_00_u03b2_2197_, v_00_u03c3_2198_, v_f_2199_, v_init_2200_, v_m_2201_);
lean_dec_ref(v_m_2201_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_x_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___boxed(lean_object* v_x_2206_, lean_object* v_x_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(v_x_2206_, v_x_2207_);
lean_dec(v_x_2207_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2209_, lean_object* v_00_u03c3_2210_, lean_object* v_f_2211_, lean_object* v_init_2212_, lean_object* v_b_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_2211_, v_init_2212_, v_b_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2215_, lean_object* v_00_u03c3_2216_, lean_object* v_f_2217_, lean_object* v_init_2218_, lean_object* v_b_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1(v_00_u03b2_2215_, v_00_u03c3_2216_, v_f_2217_, v_init_2218_, v_b_2219_);
lean_dec_ref(v_b_2219_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_2221_, lean_object* v_00_u03b2_2222_, lean_object* v_map_2223_, lean_object* v_f_2224_, lean_object* v_init_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_2223_, v_f_2224_, v_init_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_2227_, lean_object* v_00_u03b2_2228_, lean_object* v_map_2229_, lean_object* v_f_2230_, lean_object* v_init_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(v_00_u03c3_2227_, v_00_u03b2_2228_, v_map_2229_, v_f_2230_, v_init_2231_);
lean_dec_ref(v_map_2229_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5(lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___redArg(v_x_2233_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5___boxed(lean_object* v_x_2236_, lean_object* v_x_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__5(v_x_2236_, v_x_2237_);
lean_dec(v_x_2237_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2239_, lean_object* v_00_u03c3_2240_, lean_object* v_f_2241_, lean_object* v_b_2242_, lean_object* v_acc_2243_, lean_object* v_i_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2241_, v_b_2242_, v_acc_2243_, v_i_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2246_, lean_object* v_00_u03c3_2247_, lean_object* v_f_2248_, lean_object* v_b_2249_, lean_object* v_acc_2250_, lean_object* v_i_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2246_, v_00_u03c3_2247_, v_f_2248_, v_b_2249_, v_acc_2250_, v_i_2251_);
lean_dec_ref(v_b_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_map_2253_, lean_object* v_f_2254_, lean_object* v_init_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___redArg(v_f_2254_, v_map_2253_, v_init_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_map_2257_, lean_object* v_f_2258_, lean_object* v_init_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5___redArg(v_map_2257_, v_f_2258_, v_init_2259_);
lean_dec_ref(v_map_2257_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03c3_2261_, lean_object* v_00_u03b2_2262_, lean_object* v_map_2263_, lean_object* v_f_2264_, lean_object* v_init_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___redArg(v_f_2264_, v_map_2263_, v_init_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03c3_2267_, lean_object* v_00_u03b2_2268_, lean_object* v_map_2269_, lean_object* v_f_2270_, lean_object* v_init_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5(v_00_u03c3_2267_, v_00_u03b2_2268_, v_map_2269_, v_f_2270_, v_init_2271_);
lean_dec_ref(v_map_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_2273_, lean_object* v_00_u03b1_2274_, lean_object* v_00_u03b2_2275_, lean_object* v_f_2276_, lean_object* v_x_2277_, lean_object* v_x_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___redArg(v_f_2276_, v_x_2277_, v_x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_2280_, lean_object* v_00_u03b1_2281_, lean_object* v_00_u03b2_2282_, lean_object* v_f_2283_, lean_object* v_x_2284_, lean_object* v_x_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8(v_00_u03c3_2280_, v_00_u03b1_2281_, v_00_u03b2_2282_, v_f_2283_, v_x_2284_, v_x_2285_);
lean_dec_ref(v_x_2284_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12(lean_object* v_00_u03b1_2287_, lean_object* v_00_u03b2_2288_, lean_object* v_00_u03c3_2289_, lean_object* v_f_2290_, lean_object* v_as_2291_, size_t v_i_2292_, size_t v_stop_2293_, lean_object* v_b_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12___redArg(v_f_2290_, v_as_2291_, v_i_2292_, v_stop_2293_, v_b_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_00_u03b2_2297_, lean_object* v_00_u03c3_2298_, lean_object* v_f_2299_, lean_object* v_as_2300_, lean_object* v_i_2301_, lean_object* v_stop_2302_, lean_object* v_b_2303_){
_start:
{
size_t v_i_boxed_2304_; size_t v_stop_boxed_2305_; lean_object* v_res_2306_; 
v_i_boxed_2304_ = lean_unbox_usize(v_i_2301_);
lean_dec(v_i_2301_);
v_stop_boxed_2305_ = lean_unbox_usize(v_stop_2302_);
lean_dec(v_stop_2302_);
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__12(v_00_u03b1_2296_, v_00_u03b2_2297_, v_00_u03c3_2298_, v_f_2299_, v_as_2300_, v_i_boxed_2304_, v_stop_boxed_2305_, v_b_2303_);
lean_dec_ref(v_as_2300_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13(lean_object* v_00_u03c3_2307_, lean_object* v_00_u03b1_2308_, lean_object* v_00_u03b2_2309_, lean_object* v_f_2310_, lean_object* v_keys_2311_, lean_object* v_vals_2312_, lean_object* v_heq_2313_, lean_object* v_i_2314_, lean_object* v_acc_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13___redArg(v_f_2310_, v_keys_2311_, v_vals_2312_, v_i_2314_, v_acc_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13___boxed(lean_object* v_00_u03c3_2317_, lean_object* v_00_u03b1_2318_, lean_object* v_00_u03b2_2319_, lean_object* v_f_2320_, lean_object* v_keys_2321_, lean_object* v_vals_2322_, lean_object* v_heq_2323_, lean_object* v_i_2324_, lean_object* v_acc_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__5_spec__8_spec__13(v_00_u03c3_2317_, v_00_u03b1_2318_, v_00_u03b2_2319_, v_f_2320_, v_keys_2321_, v_vals_2322_, v_heq_2323_, v_i_2324_, v_acc_2325_);
lean_dec_ref(v_vals_2322_);
lean_dec_ref(v_keys_2321_);
return v_res_2326_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_xs_2329_, lean_object* v_ys_2330_, lean_object* v_x_2331_){
_start:
{
lean_object* v_zero_2332_; uint8_t v_isZero_2333_; 
v_zero_2332_ = lean_unsigned_to_nat(0u);
v_isZero_2333_ = lean_nat_dec_eq(v_x_2331_, v_zero_2332_);
if (v_isZero_2333_ == 1)
{
lean_dec(v_x_2331_);
return v_isZero_2333_;
}
else
{
lean_object* v_one_2334_; lean_object* v_n_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v_one_2334_ = lean_unsigned_to_nat(1u);
v_n_2335_ = lean_nat_sub(v_x_2331_, v_one_2334_);
lean_dec(v_x_2331_);
v___x_2336_ = lean_array_fget_borrowed(v_xs_2329_, v_n_2335_);
v___x_2337_ = lean_array_fget_borrowed(v_ys_2330_, v_n_2335_);
v___x_2338_ = lean_name_eq(v___x_2336_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_dec(v_n_2335_);
return v___x_2338_;
}
else
{
v_x_2331_ = v_n_2335_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_xs_2340_, lean_object* v_ys_2341_, lean_object* v_x_2342_){
_start:
{
uint8_t v_res_2343_; lean_object* v_r_2344_; 
v_res_2343_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_2340_, v_ys_2341_, v_x_2342_);
lean_dec_ref(v_ys_2341_);
lean_dec_ref(v_xs_2340_);
v_r_2344_ = lean_box(v_res_2343_);
return v_r_2344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_m_2345_, lean_object* v_query_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
lean_object* v_zero_2350_; uint8_t v_isZero_2351_; 
v_zero_2350_ = lean_unsigned_to_nat(0u);
v_isZero_2351_ = lean_nat_dec_eq(v_x_2348_, v_zero_2350_);
if (v_isZero_2351_ == 1)
{
lean_dec(v_x_2349_);
lean_dec(v_x_2348_);
if (lean_obj_tag(v_x_2347_) == 0)
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_box(2);
return v___x_2352_;
}
else
{
lean_object* v_val_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_val_2353_ = lean_ctor_get(v_x_2347_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_x_2347_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v_x_2347_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_val_2353_);
lean_dec(v_x_2347_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_val_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v_keyArray_2361_; lean_object* v_valueArray_2362_; lean_object* v___x_2363_; uint8_t v_isSome_2364_; 
v_keyArray_2361_ = lean_ctor_get(v_m_2345_, 1);
v_valueArray_2362_ = lean_ctor_get(v_m_2345_, 2);
v___x_2363_ = lean_array_fget_borrowed(v_keyArray_2361_, v_x_2349_);
v_isSome_2364_ = lean_noption_is_some(v___x_2363_);
if (v_isSome_2364_ == 0)
{
lean_dec(v_x_2348_);
if (lean_obj_tag(v_x_2347_) == 0)
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2365_, 0, v_x_2349_);
return v___x_2365_;
}
else
{
lean_object* v_val_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_x_2349_);
v_val_2366_ = lean_ctor_get(v_x_2347_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_x_2347_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v_x_2347_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_val_2366_);
lean_dec(v_x_2347_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_val_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_one_2374_; lean_object* v_n_2375_; lean_object* v___y_2377_; 
v_one_2374_ = lean_unsigned_to_nat(1u);
v_n_2375_ = lean_nat_sub(v_x_2348_, v_one_2374_);
lean_dec(v_x_2348_);
if (v_isSome_2364_ == 0)
{
goto v___jp_2383_;
}
else
{
lean_object* v___x_2391_; uint8_t v_isSome_2392_; 
v___x_2391_ = lean_array_fget_borrowed(v_valueArray_2362_, v_x_2349_);
v_isSome_2392_ = lean_noption_is_some(v___x_2391_);
if (v_isSome_2392_ == 0)
{
goto v___jp_2383_;
}
else
{
lean_object* v_val_2393_; lean_object* v_fst_2394_; lean_object* v_snd_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; lean_object* v_val_2398_; uint8_t v___y_2400_; uint8_t v___x_2406_; 
lean_inc(v___x_2363_);
v_val_2393_ = lean_noption_get(v___x_2363_);
v_fst_2394_ = lean_ctor_get(v_val_2393_, 0);
lean_inc(v_fst_2394_);
v_snd_2395_ = lean_ctor_get(v_val_2393_, 1);
lean_inc(v_snd_2395_);
v_fst_2396_ = lean_ctor_get(v_query_2346_, 0);
v_snd_2397_ = lean_ctor_get(v_query_2346_, 1);
lean_inc(v___x_2391_);
v_val_2398_ = lean_noption_get(v___x_2391_);
v___x_2406_ = lean_unbox(v_fst_2394_);
lean_dec(v_fst_2394_);
if (v___x_2406_ == 0)
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_unbox(v_fst_2396_);
if (v___x_2407_ == 0)
{
v___y_2400_ = v_isSome_2392_;
goto v___jp_2399_;
}
else
{
lean_dec(v_val_2398_);
lean_dec(v_snd_2395_);
lean_dec(v_val_2393_);
goto v___jp_2385_;
}
}
else
{
uint8_t v___x_2408_; 
v___x_2408_ = lean_unbox(v_fst_2396_);
v___y_2400_ = v___x_2408_;
goto v___jp_2399_;
}
v___jp_2399_:
{
if (v___y_2400_ == 0)
{
lean_dec(v_val_2398_);
lean_dec(v_snd_2395_);
lean_dec(v_val_2393_);
goto v___jp_2385_;
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2401_ = lean_array_get_size(v_snd_2395_);
v___x_2402_ = lean_array_get_size(v_snd_2397_);
v___x_2403_ = lean_nat_dec_eq(v___x_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_dec(v_val_2398_);
lean_dec(v_snd_2395_);
lean_dec(v_val_2393_);
goto v___jp_2385_;
}
else
{
uint8_t v___x_2404_; 
v___x_2404_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2395_, v_snd_2397_, v___x_2401_);
lean_dec(v_snd_2395_);
if (v___x_2404_ == 0)
{
lean_dec(v_val_2398_);
lean_dec(v_val_2393_);
goto v___jp_2385_;
}
else
{
lean_object* v___x_2405_; 
lean_dec(v_n_2375_);
lean_dec(v_x_2347_);
v___x_2405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2405_, 0, v_x_2349_);
lean_ctor_set(v___x_2405_, 1, v_val_2393_);
lean_ctor_set(v___x_2405_, 2, v_val_2398_);
return v___x_2405_;
}
}
}
}
}
}
v___jp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2378_ = lean_array_get_size(v_keyArray_2361_);
v___x_2379_ = lean_nat_add(v_x_2349_, v_one_2374_);
lean_dec(v_x_2349_);
v___x_2380_ = lean_nat_dec_lt(v___x_2379_, v___x_2378_);
if (v___x_2380_ == 0)
{
lean_dec(v___x_2379_);
v_x_2347_ = v___y_2377_;
v_x_2348_ = v_n_2375_;
v_x_2349_ = v_zero_2350_;
goto _start;
}
else
{
v_x_2347_ = v___y_2377_;
v_x_2348_ = v_n_2375_;
v_x_2349_ = v___x_2379_;
goto _start;
}
}
v___jp_2383_:
{
if (lean_obj_tag(v_x_2347_) == 0)
{
lean_object* v___x_2384_; 
lean_inc(v_x_2349_);
v___x_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2384_, 0, v_x_2349_);
v___y_2377_ = v___x_2384_;
goto v___jp_2376_;
}
else
{
v___y_2377_ = v_x_2347_;
goto v___jp_2376_;
}
}
v___jp_2385_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2386_ = lean_array_get_size(v_keyArray_2361_);
v___x_2387_ = lean_nat_add(v_x_2349_, v_one_2374_);
lean_dec(v_x_2349_);
v___x_2388_ = lean_nat_dec_lt(v___x_2387_, v___x_2386_);
if (v___x_2388_ == 0)
{
lean_dec(v___x_2387_);
v_x_2348_ = v_n_2375_;
v_x_2349_ = v_zero_2350_;
goto _start;
}
else
{
v_x_2348_ = v_n_2375_;
v_x_2349_ = v___x_2387_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_2409_, lean_object* v_query_2410_, lean_object* v_x_2411_, lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_m_2409_, v_query_2410_, v_x_2411_, v_x_2412_, v_x_2413_);
lean_dec_ref(v_query_2410_);
lean_dec_ref(v_m_2409_);
return v_res_2414_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(lean_object* v_as_2415_, size_t v_i_2416_, size_t v_stop_2417_, uint64_t v_b_2418_){
_start:
{
uint64_t v___y_2420_; uint8_t v___x_2425_; 
v___x_2425_ = lean_usize_dec_eq(v_i_2416_, v_stop_2417_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_array_uget_borrowed(v_as_2415_, v_i_2416_);
if (lean_obj_tag(v___x_2426_) == 0)
{
uint64_t v___x_2427_; 
v___x_2427_ = 1723ULL;
v___y_2420_ = v___x_2427_;
goto v___jp_2419_;
}
else
{
uint64_t v_hash_2428_; 
v_hash_2428_ = lean_ctor_get_uint64(v___x_2426_, sizeof(void*)*2);
v___y_2420_ = v_hash_2428_;
goto v___jp_2419_;
}
}
else
{
return v_b_2418_;
}
v___jp_2419_:
{
uint64_t v___x_2421_; size_t v___x_2422_; size_t v___x_2423_; 
v___x_2421_ = lean_uint64_mix_hash(v_b_2418_, v___y_2420_);
v___x_2422_ = ((size_t)1ULL);
v___x_2423_ = lean_usize_add(v_i_2416_, v___x_2422_);
v_i_2416_ = v___x_2423_;
v_b_2418_ = v___x_2421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2429_, lean_object* v_i_2430_, lean_object* v_stop_2431_, lean_object* v_b_2432_){
_start:
{
size_t v_i_boxed_2433_; size_t v_stop_boxed_2434_; uint64_t v_b_boxed_2435_; uint64_t v_res_2436_; lean_object* v_r_2437_; 
v_i_boxed_2433_ = lean_unbox_usize(v_i_2430_);
lean_dec(v_i_2430_);
v_stop_boxed_2434_ = lean_unbox_usize(v_stop_2431_);
lean_dec(v_stop_2431_);
v_b_boxed_2435_ = lean_unbox_uint64(v_b_2432_);
lean_dec_ref(v_b_2432_);
v_res_2436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_as_2429_, v_i_boxed_2433_, v_stop_boxed_2434_, v_b_boxed_2435_);
lean_dec_ref(v_as_2429_);
v_r_2437_ = lean_box_uint64(v_res_2436_);
return v_r_2437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(lean_object* v_m_2438_, lean_object* v_query_2439_){
_start:
{
lean_object* v_keyArray_2440_; lean_object* v_fst_2441_; lean_object* v_snd_2442_; lean_object* v___x_2443_; uint64_t v___y_2445_; uint64_t v___y_2446_; uint64_t v___y_2463_; uint8_t v___x_2475_; 
v_keyArray_2440_ = lean_ctor_get(v_m_2438_, 1);
v_fst_2441_ = lean_ctor_get(v_query_2439_, 0);
v_snd_2442_ = lean_ctor_get(v_query_2439_, 1);
v___x_2443_ = lean_array_get_size(v_keyArray_2440_);
v___x_2475_ = lean_unbox(v_fst_2441_);
if (v___x_2475_ == 0)
{
uint64_t v___x_2476_; 
v___x_2476_ = 13ULL;
v___y_2463_ = v___x_2476_;
goto v___jp_2462_;
}
else
{
uint64_t v___x_2477_; 
v___x_2477_ = 11ULL;
v___y_2463_ = v___x_2477_;
goto v___jp_2462_;
}
v___jp_2444_:
{
uint64_t v___x_2447_; uint64_t v___x_2448_; uint64_t v___x_2449_; uint64_t v_fold_2450_; uint64_t v___x_2451_; uint64_t v___x_2452_; uint64_t v___x_2453_; size_t v___x_2454_; size_t v___x_2455_; size_t v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2447_ = lean_uint64_mix_hash(v___y_2445_, v___y_2446_);
v___x_2448_ = 32ULL;
v___x_2449_ = lean_uint64_shift_right(v___x_2447_, v___x_2448_);
v_fold_2450_ = lean_uint64_xor(v___x_2447_, v___x_2449_);
v___x_2451_ = 16ULL;
v___x_2452_ = lean_uint64_shift_right(v_fold_2450_, v___x_2451_);
v___x_2453_ = lean_uint64_xor(v_fold_2450_, v___x_2452_);
v___x_2454_ = lean_uint64_to_usize(v___x_2453_);
v___x_2455_ = lean_usize_of_nat(v___x_2443_);
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_sub(v___x_2455_, v___x_2456_);
v___x_2458_ = lean_usize_land(v___x_2454_, v___x_2457_);
v___x_2459_ = lean_usize_to_nat(v___x_2458_);
v___x_2460_ = lean_box(0);
v___x_2461_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_m_2438_, v_query_2439_, v___x_2460_, v___x_2443_, v___x_2459_);
return v___x_2461_;
}
v___jp_2462_:
{
uint64_t v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2464_ = 7ULL;
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = lean_array_get_size(v_snd_2442_);
v___x_2467_ = lean_nat_dec_lt(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
v___y_2445_ = v___y_2463_;
v___y_2446_ = v___x_2464_;
goto v___jp_2444_;
}
else
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_nat_dec_le(v___x_2466_, v___x_2466_);
if (v___x_2468_ == 0)
{
if (v___x_2467_ == 0)
{
v___y_2445_ = v___y_2463_;
v___y_2446_ = v___x_2464_;
goto v___jp_2444_;
}
else
{
size_t v___x_2469_; size_t v___x_2470_; uint64_t v___x_2471_; 
v___x_2469_ = ((size_t)0ULL);
v___x_2470_ = lean_usize_of_nat(v___x_2466_);
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2442_, v___x_2469_, v___x_2470_, v___x_2464_);
v___y_2445_ = v___y_2463_;
v___y_2446_ = v___x_2471_;
goto v___jp_2444_;
}
}
else
{
size_t v___x_2472_; size_t v___x_2473_; uint64_t v___x_2474_; 
v___x_2472_ = ((size_t)0ULL);
v___x_2473_ = lean_usize_of_nat(v___x_2466_);
v___x_2474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2442_, v___x_2472_, v___x_2473_, v___x_2464_);
v___y_2445_ = v___y_2463_;
v___y_2446_ = v___x_2474_;
goto v___jp_2444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg___boxed(lean_object* v_m_2478_, lean_object* v_query_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_m_2478_, v_query_2479_);
lean_dec_ref(v_query_2479_);
lean_dec_ref(v_m_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10___redArg(lean_object* v_b_2481_, lean_object* v_acc_2482_, lean_object* v_i_2483_){
_start:
{
lean_object* v___y_2485_; lean_object* v_keyArray_2493_; lean_object* v_valueArray_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v_keyArray_2493_ = lean_ctor_get(v_b_2481_, 1);
v_valueArray_2494_ = lean_ctor_get(v_b_2481_, 2);
v___x_2495_ = lean_array_get_size(v_keyArray_2493_);
v___x_2496_ = lean_nat_dec_lt(v_i_2483_, v___x_2495_);
if (v___x_2496_ == 0)
{
lean_dec(v_i_2483_);
return v_acc_2482_;
}
else
{
lean_object* v___x_2497_; uint8_t v_isSome_2498_; 
v___x_2497_ = lean_array_fget_borrowed(v_keyArray_2493_, v_i_2483_);
v_isSome_2498_ = lean_noption_is_some(v___x_2497_);
if (v_isSome_2498_ == 0)
{
goto v___jp_2489_;
}
else
{
lean_object* v___x_2499_; uint8_t v_isSome_2500_; 
v___x_2499_ = lean_array_fget_borrowed(v_valueArray_2494_, v_i_2483_);
v_isSome_2500_ = lean_noption_is_some(v___x_2499_);
if (v_isSome_2500_ == 0)
{
goto v___jp_2489_;
}
else
{
lean_object* v_val_2501_; lean_object* v_val_2502_; lean_object* v_i_2504_; lean_object* v___x_2509_; 
lean_inc(v___x_2497_);
v_val_2501_ = lean_noption_get(v___x_2497_);
lean_inc(v___x_2499_);
v_val_2502_ = lean_noption_get(v___x_2499_);
v___x_2509_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_acc_2482_, v_val_2501_);
switch(lean_obj_tag(v___x_2509_))
{
case 0:
{
lean_object* v_index_2510_; lean_object* v_size_2511_; lean_object* v___x_2512_; 
v_index_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_index_2510_);
lean_dec_ref_known(v___x_2509_, 3);
v_size_2511_ = lean_ctor_get(v_acc_2482_, 0);
lean_inc(v_size_2511_);
v___x_2512_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2482_, v_size_2511_, v_index_2510_, v_val_2501_, v_val_2502_);
lean_dec(v_index_2510_);
v___y_2485_ = v___x_2512_;
goto v___jp_2484_;
}
case 1:
{
lean_object* v_index_2513_; 
v_index_2513_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_index_2513_);
lean_dec_ref_known(v___x_2509_, 1);
v_i_2504_ = v_index_2513_;
goto v___jp_2503_;
}
default: 
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2515_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2482_, v___x_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_index_2516_; 
v_index_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_index_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v_i_2504_ = v_index_2516_;
goto v___jp_2503_;
}
else
{
lean_dec(v_val_2502_);
lean_dec(v_val_2501_);
v___y_2485_ = v_acc_2482_;
goto v___jp_2484_;
}
}
}
v___jp_2503_:
{
lean_object* v_size_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_size_2505_ = lean_ctor_get(v_acc_2482_, 0);
v___x_2506_ = lean_unsigned_to_nat(1u);
v___x_2507_ = lean_nat_add(v_size_2505_, v___x_2506_);
v___x_2508_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2482_, v___x_2507_, v_i_2504_, v_val_2501_, v_val_2502_);
lean_dec(v_i_2504_);
v___y_2485_ = v___x_2508_;
goto v___jp_2484_;
}
}
}
}
v___jp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_unsigned_to_nat(1u);
v___x_2487_ = lean_nat_add(v_i_2483_, v___x_2486_);
lean_dec(v_i_2483_);
v_acc_2482_ = v___y_2485_;
v_i_2483_ = v___x_2487_;
goto _start;
}
v___jp_2489_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_unsigned_to_nat(1u);
v___x_2491_ = lean_nat_add(v_i_2483_, v___x_2490_);
lean_dec(v_i_2483_);
v_i_2483_ = v___x_2491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10___redArg___boxed(lean_object* v_b_2517_, lean_object* v_acc_2518_, lean_object* v_i_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10___redArg(v_b_2517_, v_acc_2518_, v_i_2519_);
lean_dec_ref(v_b_2517_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6___redArg(lean_object* v_init_2521_, lean_object* v_b_2522_){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_unsigned_to_nat(0u);
v___x_2524_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10___redArg(v_b_2522_, v_init_2521_, v___x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_init_2525_, lean_object* v_b_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6___redArg(v_init_2525_, v_b_2526_);
lean_dec_ref(v_b_2526_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(lean_object* v_m_2528_){
_start:
{
lean_object* v_keyArray_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_cellCount_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_target_2536_; lean_object* v___x_2537_; 
v_keyArray_2529_ = lean_ctor_get(v_m_2528_, 1);
v___x_2530_ = lean_array_get_size(v_keyArray_2529_);
v___x_2531_ = lean_unsigned_to_nat(2u);
v_cellCount_2532_ = lean_nat_mul(v___x_2530_, v___x_2531_);
v___x_2533_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2532_);
v___x_2534_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2532_);
v___x_2535_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2532_);
v_target_2536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2536_, 0, v___x_2533_);
lean_ctor_set(v_target_2536_, 1, v___x_2534_);
lean_ctor_set(v_target_2536_, 2, v___x_2535_);
v___x_2537_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6___redArg(v_target_2536_, v_m_2528_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg___boxed(lean_object* v_m_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(v_m_2538_);
lean_dec_ref(v_m_2538_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_x_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
lean_object* v_ks_2544_; lean_object* v_vs_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2584_; 
v_ks_2544_ = lean_ctor_get(v_x_2540_, 0);
v_vs_2545_ = lean_ctor_get(v_x_2540_, 1);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_x_2540_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2547_ = v_x_2540_;
v_isShared_2548_ = v_isSharedCheck_2584_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_vs_2545_);
lean_inc(v_ks_2544_);
lean_dec(v_x_2540_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2584_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2556_ = lean_array_get_size(v_ks_2544_);
v___x_2557_ = lean_nat_dec_lt(v_x_2541_, v___x_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_del_object(v___x_2547_);
lean_dec(v_x_2541_);
v___x_2558_ = lean_array_push(v_ks_2544_, v_x_2542_);
v___x_2559_ = lean_array_push(v_vs_2545_, v_x_2543_);
v___x_2560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
return v___x_2560_;
}
else
{
lean_object* v_fst_2561_; lean_object* v_snd_2562_; lean_object* v_k_x27_2563_; lean_object* v_fst_2564_; lean_object* v_snd_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2583_; 
v_fst_2561_ = lean_ctor_get(v_x_2542_, 0);
v_snd_2562_ = lean_ctor_get(v_x_2542_, 1);
v_k_x27_2563_ = lean_array_fget(v_ks_2544_, v_x_2541_);
v_fst_2564_ = lean_ctor_get(v_k_x27_2563_, 0);
v_snd_2565_ = lean_ctor_get(v_k_x27_2563_, 1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_k_x27_2563_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2567_ = v_k_x27_2563_;
v_isShared_2568_ = v_isSharedCheck_2583_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_snd_2565_);
lean_inc(v_fst_2564_);
lean_dec(v_k_x27_2563_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2583_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
uint8_t v___y_2570_; uint8_t v___x_2580_; 
v___x_2580_ = lean_unbox(v_fst_2561_);
if (v___x_2580_ == 0)
{
uint8_t v___x_2581_; 
v___x_2581_ = lean_unbox(v_fst_2564_);
lean_dec(v_fst_2564_);
if (v___x_2581_ == 0)
{
v___y_2570_ = v___x_2557_;
goto v___jp_2569_;
}
else
{
lean_del_object(v___x_2567_);
lean_dec(v_snd_2565_);
goto v___jp_2549_;
}
}
else
{
uint8_t v___x_2582_; 
v___x_2582_ = lean_unbox(v_fst_2564_);
lean_dec(v_fst_2564_);
v___y_2570_ = v___x_2582_;
goto v___jp_2569_;
}
v___jp_2569_:
{
if (v___y_2570_ == 0)
{
lean_del_object(v___x_2567_);
lean_dec(v_snd_2565_);
goto v___jp_2549_;
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2571_ = lean_array_get_size(v_snd_2562_);
v___x_2572_ = lean_array_get_size(v_snd_2565_);
v___x_2573_ = lean_nat_dec_eq(v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_del_object(v___x_2567_);
lean_dec(v_snd_2565_);
goto v___jp_2549_;
}
else
{
uint8_t v___x_2574_; 
v___x_2574_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2562_, v_snd_2565_, v___x_2571_);
lean_dec(v_snd_2565_);
if (v___x_2574_ == 0)
{
lean_del_object(v___x_2567_);
goto v___jp_2549_;
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
lean_del_object(v___x_2547_);
v___x_2575_ = lean_array_fset(v_ks_2544_, v_x_2541_, v_x_2542_);
v___x_2576_ = lean_array_fset(v_vs_2545_, v_x_2541_, v_x_2543_);
lean_dec(v_x_2541_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 1);
lean_ctor_set(v___x_2567_, 1, v___x_2576_);
lean_ctor_set(v___x_2567_, 0, v___x_2575_);
v___x_2578_ = v___x_2567_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
}
}
v___jp_2549_:
{
lean_object* v___x_2551_; 
if (v_isShared_2548_ == 0)
{
v___x_2551_ = v___x_2547_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_ks_2544_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_vs_2545_);
v___x_2551_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_unsigned_to_nat(1u);
v___x_2553_ = lean_nat_add(v_x_2541_, v___x_2552_);
lean_dec(v_x_2541_);
v_x_2540_ = v___x_2551_;
v_x_2541_ = v___x_2553_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_n_2585_, lean_object* v_k_2586_, lean_object* v_v_2587_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_n_2585_, v___x_2588_, v_k_2586_, v_v_2587_);
return v___x_2589_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(lean_object* v_x_2591_, size_t v_x_2592_, size_t v_x_2593_, lean_object* v_x_2594_, lean_object* v_x_2595_){
_start:
{
if (lean_obj_tag(v_x_2591_) == 0)
{
lean_object* v_es_2596_; size_t v___x_2597_; size_t v___x_2598_; lean_object* v_j_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_es_2596_ = lean_ctor_get(v_x_2591_, 0);
v___x_2597_ = ((size_t)31ULL);
v___x_2598_ = lean_usize_land(v_x_2592_, v___x_2597_);
v_j_2599_ = lean_usize_to_nat(v___x_2598_);
v___x_2600_ = lean_array_get_size(v_es_2596_);
v___x_2601_ = lean_nat_dec_lt(v_j_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_dec(v_j_2599_);
lean_dec(v_x_2595_);
lean_dec_ref(v_x_2594_);
return v_x_2591_;
}
else
{
lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2653_; 
lean_inc_ref(v_es_2596_);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_x_2591_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v_x_2591_, 0);
lean_dec(v_unused_2654_);
v___x_2603_ = v_x_2591_;
v_isShared_2604_ = v_isSharedCheck_2653_;
goto v_resetjp_2602_;
}
else
{
lean_dec(v_x_2591_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2653_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v_v_2605_; lean_object* v___x_2606_; lean_object* v_xs_x27_2607_; lean_object* v___y_2609_; 
v_v_2605_ = lean_array_fget(v_es_2596_, v_j_2599_);
v___x_2606_ = lean_box(0);
v_xs_x27_2607_ = lean_array_fset(v_es_2596_, v_j_2599_, v___x_2606_);
switch(lean_obj_tag(v_v_2605_))
{
case 0:
{
lean_object* v_key_2614_; lean_object* v_val_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2638_; 
v_key_2614_ = lean_ctor_get(v_v_2605_, 0);
v_val_2615_ = lean_ctor_get(v_v_2605_, 1);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_v_2605_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2617_ = v_v_2605_;
v_isShared_2618_ = v_isSharedCheck_2638_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_val_2615_);
lean_inc(v_key_2614_);
lean_dec(v_v_2605_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2638_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v_fst_2622_; lean_object* v_snd_2623_; lean_object* v_fst_2624_; lean_object* v_snd_2625_; uint8_t v___y_2627_; uint8_t v___x_2635_; 
v_fst_2622_ = lean_ctor_get(v_x_2594_, 0);
v_snd_2623_ = lean_ctor_get(v_x_2594_, 1);
v_fst_2624_ = lean_ctor_get(v_key_2614_, 0);
v_snd_2625_ = lean_ctor_get(v_key_2614_, 1);
v___x_2635_ = lean_unbox(v_fst_2622_);
if (v___x_2635_ == 0)
{
uint8_t v___x_2636_; 
v___x_2636_ = lean_unbox(v_fst_2624_);
if (v___x_2636_ == 0)
{
v___y_2627_ = v___x_2601_;
goto v___jp_2626_;
}
else
{
lean_del_object(v___x_2617_);
goto v___jp_2619_;
}
}
else
{
uint8_t v___x_2637_; 
v___x_2637_ = lean_unbox(v_fst_2624_);
v___y_2627_ = v___x_2637_;
goto v___jp_2626_;
}
v___jp_2619_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2614_, v_val_2615_, v_x_2594_, v_x_2595_);
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
v___y_2609_ = v___x_2621_;
goto v___jp_2608_;
}
v___jp_2626_:
{
if (v___y_2627_ == 0)
{
lean_del_object(v___x_2617_);
goto v___jp_2619_;
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2628_ = lean_array_get_size(v_snd_2623_);
v___x_2629_ = lean_array_get_size(v_snd_2625_);
v___x_2630_ = lean_nat_dec_eq(v___x_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_del_object(v___x_2617_);
goto v___jp_2619_;
}
else
{
uint8_t v___x_2631_; 
v___x_2631_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2623_, v_snd_2625_, v___x_2628_);
if (v___x_2631_ == 0)
{
lean_del_object(v___x_2617_);
goto v___jp_2619_;
}
else
{
lean_object* v___x_2633_; 
lean_dec(v_val_2615_);
lean_dec(v_key_2614_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 1, v_x_2595_);
lean_ctor_set(v___x_2617_, 0, v_x_2594_);
v___x_2633_ = v___x_2617_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_x_2594_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_x_2595_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
v___y_2609_ = v___x_2633_;
goto v___jp_2608_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_node_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2651_; 
v_node_2639_ = lean_ctor_get(v_v_2605_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_v_2605_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2641_ = v_v_2605_;
v_isShared_2642_ = v_isSharedCheck_2651_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_node_2639_);
lean_dec(v_v_2605_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2651_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
size_t v___x_2643_; size_t v___x_2644_; size_t v___x_2645_; size_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2643_ = ((size_t)5ULL);
v___x_2644_ = lean_usize_shift_right(v_x_2592_, v___x_2643_);
v___x_2645_ = ((size_t)1ULL);
v___x_2646_ = lean_usize_add(v_x_2593_, v___x_2645_);
v___x_2647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_node_2639_, v___x_2644_, v___x_2646_, v_x_2594_, v_x_2595_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2647_);
v___x_2649_ = v___x_2641_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
v___y_2609_ = v___x_2649_;
goto v___jp_2608_;
}
}
}
default: 
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2652_, 0, v_x_2594_);
lean_ctor_set(v___x_2652_, 1, v_x_2595_);
v___y_2609_ = v___x_2652_;
goto v___jp_2608_;
}
}
v___jp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2610_ = lean_array_fset(v_xs_x27_2607_, v_j_2599_, v___y_2609_);
lean_dec(v_j_2599_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2610_);
v___x_2612_ = v___x_2603_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
else
{
lean_object* v_ks_2655_; lean_object* v_vs_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2676_; 
v_ks_2655_ = lean_ctor_get(v_x_2591_, 0);
v_vs_2656_ = lean_ctor_get(v_x_2591_, 1);
v_isSharedCheck_2676_ = !lean_is_exclusive(v_x_2591_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2658_ = v_x_2591_;
v_isShared_2659_ = v_isSharedCheck_2676_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_vs_2656_);
lean_inc(v_ks_2655_);
lean_dec(v_x_2591_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2676_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_ks_2655_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_vs_2656_);
v___x_2661_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v_newNode_2662_; uint8_t v___y_2664_; size_t v___x_2670_; uint8_t v___x_2671_; 
v_newNode_2662_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6___redArg(v___x_2661_, v_x_2594_, v_x_2595_);
v___x_2670_ = ((size_t)7ULL);
v___x_2671_ = lean_usize_dec_le(v___x_2670_, v_x_2593_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2672_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2662_);
v___x_2673_ = lean_unsigned_to_nat(4u);
v___x_2674_ = lean_nat_dec_lt(v___x_2672_, v___x_2673_);
lean_dec(v___x_2672_);
v___y_2664_ = v___x_2674_;
goto v___jp_2663_;
}
else
{
v___y_2664_ = v___x_2671_;
goto v___jp_2663_;
}
v___jp_2663_:
{
if (v___y_2664_ == 0)
{
lean_object* v_ks_2665_; lean_object* v_vs_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_ks_2665_ = lean_ctor_get(v_newNode_2662_, 0);
lean_inc_ref(v_ks_2665_);
v_vs_2666_ = lean_ctor_get(v_newNode_2662_, 1);
lean_inc_ref(v_vs_2666_);
lean_dec_ref(v_newNode_2662_);
v___x_2667_ = lean_unsigned_to_nat(0u);
v___x_2668_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_2669_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_x_2593_, v_ks_2665_, v_vs_2666_, v___x_2667_, v___x_2668_);
lean_dec_ref(v_vs_2666_);
lean_dec_ref(v_ks_2665_);
return v___x_2669_;
}
else
{
return v_newNode_2662_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7___redArg(size_t v_depth_2677_, lean_object* v_keys_2678_, lean_object* v_vals_2679_, lean_object* v_i_2680_, lean_object* v_entries_2681_){
_start:
{
lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = lean_array_get_size(v_keys_2678_);
v___x_2683_ = lean_nat_dec_lt(v_i_2680_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_dec(v_i_2680_);
return v_entries_2681_;
}
else
{
lean_object* v_k_2684_; lean_object* v_fst_2685_; lean_object* v_snd_2686_; lean_object* v_v_2687_; uint64_t v___y_2689_; uint64_t v___y_2690_; uint64_t v___y_2703_; uint8_t v___x_2715_; 
v_k_2684_ = lean_array_fget_borrowed(v_keys_2678_, v_i_2680_);
v_fst_2685_ = lean_ctor_get(v_k_2684_, 0);
v_snd_2686_ = lean_ctor_get(v_k_2684_, 1);
v_v_2687_ = lean_array_fget_borrowed(v_vals_2679_, v_i_2680_);
v___x_2715_ = lean_unbox(v_fst_2685_);
if (v___x_2715_ == 0)
{
uint64_t v___x_2716_; 
v___x_2716_ = 13ULL;
v___y_2703_ = v___x_2716_;
goto v___jp_2702_;
}
else
{
uint64_t v___x_2717_; 
v___x_2717_ = 11ULL;
v___y_2703_ = v___x_2717_;
goto v___jp_2702_;
}
v___jp_2688_:
{
uint64_t v___x_2691_; size_t v_h_2692_; size_t v___x_2693_; lean_object* v___x_2694_; size_t v___x_2695_; size_t v___x_2696_; size_t v___x_2697_; size_t v_h_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2691_ = lean_uint64_mix_hash(v___y_2689_, v___y_2690_);
v_h_2692_ = lean_uint64_to_usize(v___x_2691_);
v___x_2693_ = ((size_t)5ULL);
v___x_2694_ = lean_unsigned_to_nat(1u);
v___x_2695_ = ((size_t)1ULL);
v___x_2696_ = lean_usize_sub(v_depth_2677_, v___x_2695_);
v___x_2697_ = lean_usize_mul(v___x_2693_, v___x_2696_);
v_h_2698_ = lean_usize_shift_right(v_h_2692_, v___x_2697_);
v___x_2699_ = lean_nat_add(v_i_2680_, v___x_2694_);
lean_dec(v_i_2680_);
lean_inc(v_v_2687_);
lean_inc(v_k_2684_);
v___x_2700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_entries_2681_, v_h_2698_, v_depth_2677_, v_k_2684_, v_v_2687_);
v_i_2680_ = v___x_2699_;
v_entries_2681_ = v___x_2700_;
goto _start;
}
v___jp_2702_:
{
uint64_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2704_ = 7ULL;
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = lean_array_get_size(v_snd_2686_);
v___x_2707_ = lean_nat_dec_lt(v___x_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
v___y_2689_ = v___y_2703_;
v___y_2690_ = v___x_2704_;
goto v___jp_2688_;
}
else
{
uint8_t v___x_2708_; 
v___x_2708_ = lean_nat_dec_le(v___x_2706_, v___x_2706_);
if (v___x_2708_ == 0)
{
if (v___x_2707_ == 0)
{
v___y_2689_ = v___y_2703_;
v___y_2690_ = v___x_2704_;
goto v___jp_2688_;
}
else
{
size_t v___x_2709_; size_t v___x_2710_; uint64_t v___x_2711_; 
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = lean_usize_of_nat(v___x_2706_);
v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2686_, v___x_2709_, v___x_2710_, v___x_2704_);
v___y_2689_ = v___y_2703_;
v___y_2690_ = v___x_2711_;
goto v___jp_2688_;
}
}
else
{
size_t v___x_2712_; size_t v___x_2713_; uint64_t v___x_2714_; 
v___x_2712_ = ((size_t)0ULL);
v___x_2713_ = lean_usize_of_nat(v___x_2706_);
v___x_2714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2686_, v___x_2712_, v___x_2713_, v___x_2704_);
v___y_2689_ = v___y_2703_;
v___y_2690_ = v___x_2714_;
goto v___jp_2688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_depth_2718_, lean_object* v_keys_2719_, lean_object* v_vals_2720_, lean_object* v_i_2721_, lean_object* v_entries_2722_){
_start:
{
size_t v_depth_boxed_2723_; lean_object* v_res_2724_; 
v_depth_boxed_2723_ = lean_unbox_usize(v_depth_2718_);
lean_dec(v_depth_2718_);
v_res_2724_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_depth_boxed_2723_, v_keys_2719_, v_vals_2720_, v_i_2721_, v_entries_2722_);
lean_dec_ref(v_vals_2720_);
lean_dec_ref(v_keys_2719_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_2725_, lean_object* v_x_2726_, lean_object* v_x_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_){
_start:
{
size_t v_x_2133__boxed_2730_; size_t v_x_2134__boxed_2731_; lean_object* v_res_2732_; 
v_x_2133__boxed_2730_ = lean_unbox_usize(v_x_2726_);
lean_dec(v_x_2726_);
v_x_2134__boxed_2731_ = lean_unbox_usize(v_x_2727_);
lean_dec(v_x_2727_);
v_res_2732_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_x_2725_, v_x_2133__boxed_2730_, v_x_2134__boxed_2731_, v_x_2728_, v_x_2729_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(lean_object* v_x_2733_, lean_object* v_x_2734_, lean_object* v_x_2735_){
_start:
{
uint64_t v___y_2737_; uint64_t v___y_2738_; lean_object* v_fst_2743_; lean_object* v_snd_2744_; uint64_t v___y_2746_; uint8_t v___x_2758_; 
v_fst_2743_ = lean_ctor_get(v_x_2734_, 0);
v_snd_2744_ = lean_ctor_get(v_x_2734_, 1);
v___x_2758_ = lean_unbox(v_fst_2743_);
if (v___x_2758_ == 0)
{
uint64_t v___x_2759_; 
v___x_2759_ = 13ULL;
v___y_2746_ = v___x_2759_;
goto v___jp_2745_;
}
else
{
uint64_t v___x_2760_; 
v___x_2760_ = 11ULL;
v___y_2746_ = v___x_2760_;
goto v___jp_2745_;
}
v___jp_2736_:
{
uint64_t v___x_2739_; size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2739_ = lean_uint64_mix_hash(v___y_2737_, v___y_2738_);
v___x_2740_ = lean_uint64_to_usize(v___x_2739_);
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_x_2733_, v___x_2740_, v___x_2741_, v_x_2734_, v_x_2735_);
return v___x_2742_;
}
v___jp_2745_:
{
uint64_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2747_ = 7ULL;
v___x_2748_ = lean_unsigned_to_nat(0u);
v___x_2749_ = lean_array_get_size(v_snd_2744_);
v___x_2750_ = lean_nat_dec_lt(v___x_2748_, v___x_2749_);
if (v___x_2750_ == 0)
{
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___x_2747_;
goto v___jp_2736_;
}
else
{
uint8_t v___x_2751_; 
v___x_2751_ = lean_nat_dec_le(v___x_2749_, v___x_2749_);
if (v___x_2751_ == 0)
{
if (v___x_2750_ == 0)
{
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___x_2747_;
goto v___jp_2736_;
}
else
{
size_t v___x_2752_; size_t v___x_2753_; uint64_t v___x_2754_; 
v___x_2752_ = ((size_t)0ULL);
v___x_2753_ = lean_usize_of_nat(v___x_2749_);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2744_, v___x_2752_, v___x_2753_, v___x_2747_);
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___x_2754_;
goto v___jp_2736_;
}
}
else
{
size_t v___x_2755_; size_t v___x_2756_; uint64_t v___x_2757_; 
v___x_2755_ = ((size_t)0ULL);
v___x_2756_ = lean_usize_of_nat(v___x_2749_);
v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2744_, v___x_2755_, v___x_2756_, v___x_2747_);
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___x_2757_;
goto v___jp_2736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(lean_object* v_x_2761_, lean_object* v_x_2762_, lean_object* v_x_2763_){
_start:
{
uint8_t v_stage_u2081_2764_; lean_object* v_map_u2081_2765_; lean_object* v_map_u2082_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2846_; 
v_stage_u2081_2764_ = lean_ctor_get_uint8(v_x_2761_, sizeof(void*)*2);
v_map_u2081_2765_ = lean_ctor_get(v_x_2761_, 0);
v_map_u2082_2766_ = lean_ctor_get(v_x_2761_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_x_2761_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2768_ = v_x_2761_;
v_isShared_2769_ = v_isSharedCheck_2846_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_map_u2082_2766_);
lean_inc(v_map_u2081_2765_);
lean_dec(v_x_2761_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2846_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___y_2771_; lean_object* v_i_2772_; lean_object* v___y_2781_; lean_object* v___y_2793_; lean_object* v_i_2794_; 
if (v_stage_u2081_2764_ == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_del_object(v___x_2768_);
v___x_2812_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_map_u2082_2766_, v_x_2762_, v_x_2763_);
v___x_2813_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2813_, 0, v_map_u2081_2765_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*2, v_stage_u2081_2764_);
return v___x_2813_;
}
else
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_map_u2081_2765_, v_x_2762_);
switch(lean_obj_tag(v___x_2814_))
{
case 0:
{
lean_object* v_index_2815_; lean_object* v_size_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_del_object(v___x_2768_);
v_index_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_index_2815_);
lean_dec_ref_known(v___x_2814_, 3);
v_size_2816_ = lean_ctor_get(v_map_u2081_2765_, 0);
lean_inc(v_size_2816_);
v___x_2817_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_2765_, v_size_2816_, v_index_2815_, v_x_2762_, v_x_2763_);
lean_dec(v_index_2815_);
v___x_2818_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v_map_u2082_2766_);
lean_ctor_set_uint8(v___x_2818_, sizeof(void*)*2, v_stage_u2081_2764_);
return v___x_2818_;
}
case 1:
{
lean_object* v_index_2819_; lean_object* v_size_2820_; lean_object* v_keyArray_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
lean_del_object(v___x_2768_);
v_index_2819_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_index_2819_);
lean_dec_ref_known(v___x_2814_, 1);
v_size_2820_ = lean_ctor_get(v_map_u2081_2765_, 0);
v_keyArray_2821_ = lean_ctor_get(v_map_u2081_2765_, 1);
v___x_2822_ = lean_unsigned_to_nat(1u);
v___x_2823_ = lean_nat_add(v_size_2820_, v___x_2822_);
v___x_2824_ = lean_array_get_size(v_keyArray_2821_);
v___x_2825_ = lean_nat_dec_lt(v___x_2823_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_dec(v___x_2823_);
lean_dec(v_index_2819_);
goto v___jp_2800_;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v___x_2826_ = lean_unsigned_to_nat(4u);
v___x_2827_ = lean_nat_mul(v___x_2823_, v___x_2826_);
v___x_2828_ = lean_unsigned_to_nat(3u);
v___x_2829_ = lean_nat_mul(v___x_2824_, v___x_2828_);
v___x_2830_ = lean_nat_dec_le(v___x_2827_, v___x_2829_);
lean_dec(v___x_2829_);
lean_dec(v___x_2827_);
if (v___x_2830_ == 0)
{
lean_dec(v___x_2823_);
lean_dec(v_index_2819_);
goto v___jp_2800_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_2765_, v___x_2823_, v_index_2819_, v_x_2762_, v_x_2763_);
lean_dec(v_index_2819_);
v___x_2832_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
lean_ctor_set(v___x_2832_, 1, v_map_u2082_2766_);
lean_ctor_set_uint8(v___x_2832_, sizeof(void*)*2, v_stage_u2081_2764_);
return v___x_2832_;
}
}
}
default: 
{
lean_object* v_size_2833_; lean_object* v_keyArray_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v_size_2833_ = lean_ctor_get(v_map_u2081_2765_, 0);
v_keyArray_2834_ = lean_ctor_get(v_map_u2081_2765_, 1);
v___x_2835_ = lean_unsigned_to_nat(1u);
v___x_2836_ = lean_nat_add(v_size_2833_, v___x_2835_);
v___x_2837_ = lean_array_get_size(v_keyArray_2834_);
v___x_2838_ = lean_nat_dec_lt(v___x_2836_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; 
lean_dec(v___x_2836_);
v___x_2839_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(v_map_u2081_2765_);
lean_dec_ref(v_map_u2081_2765_);
v___y_2781_ = v___x_2839_;
goto v___jp_2780_;
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2840_ = lean_unsigned_to_nat(4u);
v___x_2841_ = lean_nat_mul(v___x_2836_, v___x_2840_);
lean_dec(v___x_2836_);
v___x_2842_ = lean_unsigned_to_nat(3u);
v___x_2843_ = lean_nat_mul(v___x_2837_, v___x_2842_);
v___x_2844_ = lean_nat_dec_le(v___x_2841_, v___x_2843_);
lean_dec(v___x_2843_);
lean_dec(v___x_2841_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; 
v___x_2845_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(v_map_u2081_2765_);
lean_dec_ref(v_map_u2081_2765_);
v___y_2781_ = v___x_2845_;
goto v___jp_2780_;
}
else
{
v___y_2781_ = v_map_u2081_2765_;
goto v___jp_2780_;
}
}
}
}
}
v___jp_2770_:
{
lean_object* v_size_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v_size_2773_ = lean_ctor_get(v___y_2771_, 0);
v___x_2774_ = lean_unsigned_to_nat(1u);
v___x_2775_ = lean_nat_add(v_size_2773_, v___x_2774_);
v___x_2776_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2771_, v___x_2775_, v_i_2772_, v_x_2762_, v_x_2763_);
lean_dec(v_i_2772_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2776_);
v___x_2778_ = v___x_2768_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_map_u2082_2766_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, sizeof(void*)*2, v_stage_u2081_2764_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
v___jp_2780_:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v___y_2781_, v_x_2762_);
switch(lean_obj_tag(v___x_2782_))
{
case 0:
{
lean_object* v_index_2783_; lean_object* v_size_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_del_object(v___x_2768_);
v_index_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_index_2783_);
lean_dec_ref_known(v___x_2782_, 3);
v_size_2784_ = lean_ctor_get(v___y_2781_, 0);
lean_inc(v_size_2784_);
v___x_2785_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2781_, v_size_2784_, v_index_2783_, v_x_2762_, v_x_2763_);
lean_dec(v_index_2783_);
v___x_2786_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v_map_u2082_2766_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*2, v_stage_u2081_2764_);
return v___x_2786_;
}
case 1:
{
lean_object* v_index_2787_; 
v_index_2787_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_index_2787_);
lean_dec_ref_known(v___x_2782_, 1);
v___y_2771_ = v___y_2781_;
v_i_2772_ = v_index_2787_;
goto v___jp_2770_;
}
default: 
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_unsigned_to_nat(0u);
v___x_2789_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2781_, v___x_2788_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_index_2790_; 
v_index_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_index_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___y_2771_ = v___y_2781_;
v_i_2772_ = v_index_2790_;
goto v___jp_2770_;
}
else
{
lean_object* v___x_2791_; 
lean_del_object(v___x_2768_);
lean_dec(v_x_2763_);
lean_dec_ref(v_x_2762_);
v___x_2791_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2791_, 0, v___y_2781_);
lean_ctor_set(v___x_2791_, 1, v_map_u2082_2766_);
lean_ctor_set_uint8(v___x_2791_, sizeof(void*)*2, v_stage_u2081_2764_);
return v___x_2791_;
}
}
}
}
v___jp_2792_:
{
lean_object* v_size_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_size_2795_ = lean_ctor_get(v___y_2793_, 0);
v___x_2796_ = lean_unsigned_to_nat(1u);
v___x_2797_ = lean_nat_add(v_size_2795_, v___x_2796_);
v___x_2798_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2793_, v___x_2797_, v_i_2794_, v_x_2762_, v_x_2763_);
lean_dec(v_i_2794_);
v___x_2799_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v_map_u2082_2766_);
lean_ctor_set_uint8(v___x_2799_, sizeof(void*)*2, v_stage_u2081_2764_);
return v___x_2799_;
}
v___jp_2800_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(v_map_u2081_2765_);
lean_dec_ref(v_map_u2081_2765_);
v___x_2802_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v___x_2801_, v_x_2762_);
switch(lean_obj_tag(v___x_2802_))
{
case 0:
{
lean_object* v_index_2803_; lean_object* v_size_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_index_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_index_2803_);
lean_dec_ref_known(v___x_2802_, 3);
v_size_2804_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_size_2804_);
v___x_2805_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2801_, v_size_2804_, v_index_2803_, v_x_2762_, v_x_2763_);
lean_dec(v_index_2803_);
v___x_2806_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
lean_ctor_set(v___x_2806_, 1, v_map_u2082_2766_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*2, v_stage_u2081_2764_);
return v___x_2806_;
}
case 1:
{
lean_object* v_index_2807_; 
v_index_2807_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_index_2807_);
lean_dec_ref_known(v___x_2802_, 1);
v___y_2793_ = v___x_2801_;
v_i_2794_ = v_index_2807_;
goto v___jp_2792_;
}
default: 
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = lean_unsigned_to_nat(0u);
v___x_2809_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2801_, v___x_2808_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_index_2810_; 
v_index_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_index_2810_);
lean_dec_ref_known(v___x_2809_, 1);
v___y_2793_ = v___x_2801_;
v_i_2794_ = v_index_2810_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2811_; 
lean_dec(v_x_2763_);
lean_dec_ref(v_x_2762_);
v___x_2811_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2811_, 0, v___x_2801_);
lean_ctor_set(v___x_2811_, 1, v_map_u2082_2766_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*2, v_stage_u2081_2764_);
return v___x_2811_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminatorEntry(lean_object* v_es_2847_, lean_object* v_e_2848_){
_start:
{
uint8_t v_induction_2849_; lean_object* v_typeNames_2850_; lean_object* v_elimName_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_induction_2849_ = lean_ctor_get_uint8(v_e_2848_, sizeof(void*)*2);
v_typeNames_2850_ = lean_ctor_get(v_e_2848_, 0);
lean_inc_ref(v_typeNames_2850_);
v_elimName_2851_ = lean_ctor_get(v_e_2848_, 1);
lean_inc(v_elimName_2851_);
lean_dec_ref(v_e_2848_);
v___x_2852_ = lean_box(v_induction_2849_);
v___x_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v_typeNames_2850_);
v___x_2854_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(v_es_2847_, v___x_2853_, v_elimName_2851_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0(lean_object* v_00_u03b2_2855_, lean_object* v_x_2856_, lean_object* v_x_2857_, lean_object* v_x_2858_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(v_x_2856_, v_x_2857_, v_x_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(lean_object* v_00_u03b2_2860_, lean_object* v_m_2861_, lean_object* v_query_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_m_2861_, v_query_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2864_, lean_object* v_m_2865_, lean_object* v_query_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(v_00_u03b2_2864_, v_m_2865_, v_query_2866_);
lean_dec_ref(v_query_2866_);
lean_dec_ref(v_m_2865_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1(lean_object* v_00_u03b2_2868_, lean_object* v_x_2869_, lean_object* v_x_2870_, lean_object* v_x_2871_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_x_2869_, v_x_2870_, v_x_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2(lean_object* v_00_u03b2_2873_, lean_object* v_m_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(v_m_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2876_, lean_object* v_m_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2(v_00_u03b2_2876_, v_m_2877_);
lean_dec_ref(v_m_2877_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2879_, lean_object* v_m_2880_, lean_object* v_query_2881_, lean_object* v_x_2882_, lean_object* v_x_2883_, lean_object* v_x_2884_, lean_object* v_x_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_m_2880_, v_query_2881_, v_x_2882_, v_x_2883_, v_x_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2887_, lean_object* v_m_2888_, lean_object* v_query_2889_, lean_object* v_x_2890_, lean_object* v_x_2891_, lean_object* v_x_2892_, lean_object* v_x_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(v_00_u03b2_2887_, v_m_2888_, v_query_2889_, v_x_2890_, v_x_2891_, v_x_2892_, v_x_2893_);
lean_dec_ref(v_query_2889_);
lean_dec_ref(v_m_2888_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2895_, lean_object* v_x_2896_, size_t v_x_2897_, size_t v_x_2898_, lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_x_2896_, v_x_2897_, v_x_2898_, v_x_2899_, v_x_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2902_, lean_object* v_x_2903_, lean_object* v_x_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_){
_start:
{
size_t v_x_2583__boxed_2908_; size_t v_x_2584__boxed_2909_; lean_object* v_res_2910_; 
v_x_2583__boxed_2908_ = lean_unbox_usize(v_x_2904_);
lean_dec(v_x_2904_);
v_x_2584__boxed_2909_ = lean_unbox_usize(v_x_2905_);
lean_dec(v_x_2905_);
v_res_2910_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(v_00_u03b2_2902_, v_x_2903_, v_x_2583__boxed_2908_, v_x_2584__boxed_2909_, v_x_2906_, v_x_2907_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2911_, lean_object* v_init_2912_, lean_object* v_b_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6___redArg(v_init_2912_, v_b_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2915_, lean_object* v_init_2916_, lean_object* v_b_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6(v_00_u03b2_2915_, v_init_2916_, v_b_2917_);
lean_dec_ref(v_b_2917_);
return v_res_2918_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_xs_2919_, lean_object* v_ys_2920_, lean_object* v_hsz_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
uint8_t v___x_2924_; 
v___x_2924_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_2919_, v_ys_2920_, v_x_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_xs_2925_, lean_object* v_ys_2926_, lean_object* v_hsz_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
uint8_t v_res_2930_; lean_object* v_r_2931_; 
v_res_2930_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(v_xs_2925_, v_ys_2926_, v_hsz_2927_, v_x_2928_, v_x_2929_);
lean_dec_ref(v_ys_2926_);
lean_dec_ref(v_xs_2925_);
v_r_2931_ = lean_box(v_res_2930_);
return v_r_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_2932_, lean_object* v_n_2933_, lean_object* v_k_2934_, lean_object* v_v_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6___redArg(v_n_2933_, v_k_2934_, v_v_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_2937_, size_t v_depth_2938_, lean_object* v_keys_2939_, lean_object* v_vals_2940_, lean_object* v_heq_2941_, lean_object* v_i_2942_, lean_object* v_entries_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_depth_2938_, v_keys_2939_, v_vals_2940_, v_i_2942_, v_entries_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_2945_, lean_object* v_depth_2946_, lean_object* v_keys_2947_, lean_object* v_vals_2948_, lean_object* v_heq_2949_, lean_object* v_i_2950_, lean_object* v_entries_2951_){
_start:
{
size_t v_depth_boxed_2952_; lean_object* v_res_2953_; 
v_depth_boxed_2952_ = lean_unbox_usize(v_depth_2946_);
lean_dec(v_depth_2946_);
v_res_2953_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__7(v_00_u03b2_2945_, v_depth_boxed_2952_, v_keys_2947_, v_vals_2948_, v_heq_2949_, v_i_2950_, v_entries_2951_);
lean_dec_ref(v_vals_2948_);
lean_dec_ref(v_keys_2947_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10(lean_object* v_00_u03b2_2954_, lean_object* v_b_2955_, lean_object* v_acc_2956_, lean_object* v_i_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10___redArg(v_b_2955_, v_acc_2956_, v_i_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2959_, lean_object* v_b_2960_, lean_object* v_acc_2961_, lean_object* v_i_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2_spec__6_spec__10(v_00_u03b2_2959_, v_b_2960_, v_acc_2961_, v_i_2962_);
lean_dec_ref(v_b_2960_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_2964_, lean_object* v_x_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_, lean_object* v_x_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_x_2965_, v_x_2966_, v_x_2967_, v_x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_2970_){
_start:
{
uint8_t v_stage_u2081_2971_; 
v_stage_u2081_2971_ = lean_ctor_get_uint8(v_m_2970_, sizeof(void*)*2);
if (v_stage_u2081_2971_ == 0)
{
return v_m_2970_;
}
else
{
lean_object* v_map_u2081_2972_; lean_object* v_map_u2082_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2981_; 
v_map_u2081_2972_ = lean_ctor_get(v_m_2970_, 0);
v_map_u2082_2973_ = lean_ctor_get(v_m_2970_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_m_2970_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2975_ = v_m_2970_;
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_map_u2082_2973_);
lean_inc(v_map_u2081_2972_);
lean_dec(v_m_2970_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
uint8_t v___x_2977_; lean_object* v___x_2979_; 
v___x_2977_ = 0;
if (v_isShared_2976_ == 0)
{
v___x_2979_ = v___x_2975_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_map_u2081_2972_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_map_u2082_2973_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_ctor_set_uint8(v___x_2979_, sizeof(void*)*2, v___x_2977_);
return v___x_2979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_2982_, lean_object* v_m_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(v_m_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(lean_object* v_x_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_a_2986_);
lean_inc_ref_n(v___x_2987_, 2);
v___x_2988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
lean_ctor_set(v___x_2988_, 2, v___x_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object* v_x_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(v_x_2989_, v_a_2990_);
lean_dec_ref(v_x_2989_);
return v_res_2991_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3002_; lean_object* v___f_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___f_3002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___f_3003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_3004_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__5, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__5_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__5);
v___x_3005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_3006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_3007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
lean_ctor_set(v___x_3007_, 1, v___x_3005_);
lean_ctor_set(v___x_3007_, 2, v___x_3004_);
lean_ctor_set(v___x_3007_, 3, v___f_3003_);
lean_ctor_set(v___x_3007_, 4, v___f_3002_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_);
v___x_3010_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
return v_res_3012_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(lean_object* v_x_3013_){
_start:
{
uint8_t v___x_3014_; 
v___x_3014_ = 0;
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed(lean_object* v_x_3015_){
_start:
{
uint8_t v_res_3016_; lean_object* v_r_3017_; 
v_res_3016_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(v_x_3015_);
lean_dec(v_x_3015_);
v_r_3017_ = lean_box(v_res_3016_);
return v_r_3017_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(lean_object* v_fvarId_3018_, lean_object* v_x_3019_){
_start:
{
uint8_t v___x_3020_; 
v___x_3020_ = l_Lean_instBEqFVarId_beq(v_fvarId_3018_, v_x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_3021_, lean_object* v_x_3022_){
_start:
{
uint8_t v_res_3023_; lean_object* v_r_3024_; 
v_res_3023_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(v_fvarId_3021_, v_x_3022_);
lean_dec(v_x_3022_);
lean_dec(v_fvarId_3021_);
v_r_3024_ = lean_box(v_res_3023_);
return v_r_3024_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_3026_; lean_object* v___x_3027_; 
v_cellCount_3026_ = lean_unsigned_to_nat(16u);
v___x_3027_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3026_);
return v___x_3027_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_3028_; lean_object* v___x_3029_; 
v_cellCount_3028_ = lean_unsigned_to_nat(16u);
v___x_3029_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3028_);
return v___x_3029_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3030_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2);
v___x_3031_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1);
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3031_);
lean_ctor_set(v___x_3033_, 2, v___x_3030_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(lean_object* v_e_3034_, lean_object* v_fvarId_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; uint8_t v_fst_3040_; lean_object* v_mctx_3041_; lean_object* v___y_3059_; lean_object* v_mctx_3064_; lean_object* v___f_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3038_ = lean_st_ref_get(v___y_3036_);
v_mctx_3064_ = lean_ctor_get(v___x_3038_, 0);
lean_inc_ref_n(v_mctx_3064_, 2);
lean_dec(v___x_3038_);
v___f_3065_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0));
v___f_3066_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3066_, 0, v_fvarId_3035_);
v___x_3067_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__3, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__3_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__3);
v___x_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v_mctx_3064_);
v___x_3069_ = l_Lean_Expr_hasFVar(v_e_3034_);
if (v___x_3069_ == 0)
{
uint8_t v___x_3070_; 
v___x_3070_ = l_Lean_Expr_hasMVar(v_e_3034_);
if (v___x_3070_ == 0)
{
lean_dec_ref_known(v___x_3068_, 2);
lean_dec_ref(v___f_3066_);
lean_dec_ref(v_e_3034_);
v_fst_3040_ = v___x_3070_;
v_mctx_3041_ = v_mctx_3064_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3071_; 
lean_dec_ref(v_mctx_3064_);
v___x_3071_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3066_, v___f_3065_, v_e_3034_, v___x_3068_);
v___y_3059_ = v___x_3071_;
goto v___jp_3058_;
}
}
else
{
lean_object* v___x_3072_; 
lean_dec_ref(v_mctx_3064_);
v___x_3072_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3066_, v___f_3065_, v_e_3034_, v___x_3068_);
v___y_3059_ = v___x_3072_;
goto v___jp_3058_;
}
v___jp_3039_:
{
lean_object* v___x_3042_; lean_object* v_cache_3043_; lean_object* v_zetaDeltaFVarIds_3044_; lean_object* v_postponed_3045_; lean_object* v_diag_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3056_; 
v___x_3042_ = lean_st_ref_take(v___y_3036_);
v_cache_3043_ = lean_ctor_get(v___x_3042_, 1);
v_zetaDeltaFVarIds_3044_ = lean_ctor_get(v___x_3042_, 2);
v_postponed_3045_ = lean_ctor_get(v___x_3042_, 3);
v_diag_3046_ = lean_ctor_get(v___x_3042_, 4);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___x_3042_, 0);
lean_dec(v_unused_3057_);
v___x_3048_ = v___x_3042_;
v_isShared_3049_ = v_isSharedCheck_3056_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_diag_3046_);
lean_inc(v_postponed_3045_);
lean_inc(v_zetaDeltaFVarIds_3044_);
lean_inc(v_cache_3043_);
lean_dec(v___x_3042_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3056_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v_mctx_3041_);
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_mctx_3041_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_cache_3043_);
lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_zetaDeltaFVarIds_3044_);
lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_postponed_3045_);
lean_ctor_set(v_reuseFailAlloc_3055_, 4, v_diag_3046_);
v___x_3051_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = lean_st_ref_put(v___y_3036_, v___x_3051_);
v___x_3053_ = lean_box(v_fst_3040_);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
return v___x_3054_;
}
}
}
v___jp_3058_:
{
lean_object* v_snd_3060_; lean_object* v_fst_3061_; lean_object* v_mctx_3062_; uint8_t v___x_3063_; 
v_snd_3060_ = lean_ctor_get(v___y_3059_, 1);
lean_inc(v_snd_3060_);
v_fst_3061_ = lean_ctor_get(v___y_3059_, 0);
lean_inc(v_fst_3061_);
lean_dec_ref(v___y_3059_);
v_mctx_3062_ = lean_ctor_get(v_snd_3060_, 1);
lean_inc_ref(v_mctx_3062_);
lean_dec(v_snd_3060_);
v___x_3063_ = lean_unbox(v_fst_3061_);
lean_dec(v_fst_3061_);
v_fst_3040_ = v___x_3063_;
v_mctx_3041_ = v_mctx_3062_;
goto v___jp_3039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___boxed(lean_object* v_e_3073_, lean_object* v_fvarId_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_e_3073_, v_fvarId_3074_, v___y_3075_);
lean_dec(v___y_3075_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(lean_object* v_e_3078_, lean_object* v_fvarId_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_e_3078_, v_fvarId_3079_, v___y_3081_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___boxed(lean_object* v_e_3086_, lean_object* v_fvarId_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(v_e_3086_, v_fvarId_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(lean_object* v_upperBound_3097_, lean_object* v___x_3098_, lean_object* v_xs_3099_, lean_object* v___x_3100_, lean_object* v_a_3101_, lean_object* v_b_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
uint8_t v___x_3108_; 
v___x_3108_ = lean_nat_dec_lt(v_a_3101_, v_upperBound_3097_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
lean_dec(v_a_3101_);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v_b_3102_);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_dec_ref(v_b_3102_);
v___x_3110_ = l_Lean_instInhabitedExpr;
v___x_3111_ = lean_array_fget_borrowed(v___x_3098_, v_a_3101_);
v___x_3112_ = lean_array_get_borrowed(v___x_3110_, v_xs_3099_, v___x_3111_);
lean_inc(v___y_3106_);
lean_inc_ref(v___y_3105_);
lean_inc(v___y_3104_);
lean_inc_ref(v___y_3103_);
lean_inc(v___x_3112_);
v___x_3113_ = lean_infer_type(v___x_3112_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v___x_3115_ = l_Lean_Expr_fvarId_x21(v___x_3100_);
v___x_3116_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_a_3114_, v___x_3115_, v___y_3104_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3132_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3132_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3132_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3121_ = lean_box(0);
v___x_3122_ = lean_unbox(v_a_3117_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
lean_del_object(v___x_3119_);
lean_dec(v_a_3117_);
v___x_3123_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0));
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_nat_add(v_a_3101_, v___x_3124_);
lean_dec(v_a_3101_);
v_a_3101_ = v___x_3125_;
v_b_3102_ = v___x_3123_;
goto _start;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3130_; 
lean_dec(v_a_3101_);
v___x_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3127_, 0, v_a_3117_);
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set(v___x_3128_, 1, v___x_3121_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3128_);
v___x_3130_ = v___x_3119_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec(v_a_3101_);
v_a_3133_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3116_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3116_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec(v_a_3101_);
v_a_3141_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3113_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3113_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___boxed(lean_object* v_upperBound_3149_, lean_object* v___x_3150_, lean_object* v_xs_3151_, lean_object* v___x_3152_, lean_object* v_a_3153_, lean_object* v_b_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v_upperBound_3149_, v___x_3150_, v_xs_3151_, v___x_3152_, v_a_3153_, v_b_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v___x_3152_);
lean_dec_ref(v_xs_3151_);
lean_dec_ref(v___x_3150_);
lean_dec(v_upperBound_3149_);
return v_res_3160_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0));
v___x_3163_ = l_Lean_stringToMessageData(v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(lean_object* v_upperBound_3164_, lean_object* v___x_3165_, lean_object* v___x_3166_, lean_object* v_xs_3167_, lean_object* v_a_3168_, lean_object* v_b_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_a_3176_; uint8_t v___x_3180_; 
v___x_3180_ = lean_nat_dec_lt(v_a_3168_, v_upperBound_3164_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
lean_dec(v_a_3168_);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_b_3169_);
return v___x_3181_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3182_ = l_Lean_instInhabitedExpr;
v___x_3183_ = lean_unsigned_to_nat(1u);
v___x_3184_ = lean_nat_add(v_a_3168_, v___x_3183_);
v___x_3185_ = lean_array_fget_borrowed(v___x_3166_, v_a_3168_);
v___x_3186_ = lean_array_get_borrowed(v___x_3182_, v_xs_3167_, v___x_3185_);
v___x_3213_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0));
v___x_3214_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v___x_3165_, v___x_3166_, v_xs_3167_, v___x_3186_, v___x_3184_, v___x_3213_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v_fst_3216_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___x_3214_, 1);
v_fst_3216_ = lean_ctor_get(v_a_3215_, 0);
lean_inc(v_fst_3216_);
lean_dec(v_a_3215_);
if (lean_obj_tag(v_fst_3216_) == 0)
{
goto v___jp_3187_;
}
else
{
lean_object* v_val_3217_; uint8_t v___x_3218_; 
v_val_3217_ = lean_ctor_get(v_fst_3216_, 0);
lean_inc(v_val_3217_);
lean_dec_ref_known(v_fst_3216_, 1);
v___x_3218_ = lean_unbox(v_val_3217_);
lean_dec(v_val_3217_);
if (v___x_3218_ == 0)
{
goto v___jp_3187_;
}
else
{
v_a_3176_ = v_b_3169_;
goto v___jp_3175_;
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v_b_3169_);
lean_dec(v_a_3168_);
v_a_3219_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3214_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3214_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
v___jp_3187_:
{
lean_object* v___x_3188_; 
lean_inc(v___y_3173_);
lean_inc_ref(v___y_3172_);
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
lean_inc(v___x_3186_);
v___x_3188_ = lean_infer_type(v___x_3186_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3190_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
v___x_3190_ = l_Lean_Expr_getAppFn(v_a_3189_);
if (lean_obj_tag(v___x_3190_) == 4)
{
lean_object* v_declName_3191_; lean_object* v___x_3192_; 
lean_dec(v_a_3189_);
v_declName_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_declName_3191_);
lean_dec_ref_known(v___x_3190_, 2);
v___x_3192_ = lean_array_push(v_b_3169_, v_declName_3191_);
v_a_3176_ = v___x_3192_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
lean_dec_ref(v___x_3190_);
v___x_3193_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1);
v___x_3194_ = l_Lean_indentExpr(v_a_3189_);
v___x_3195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3193_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_3195_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_dec_ref_known(v___x_3196_, 1);
v_a_3176_ = v_b_3169_;
goto v___jp_3175_;
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec_ref(v_b_3169_);
lean_dec(v_a_3168_);
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v_b_3169_);
lean_dec(v_a_3168_);
v_a_3205_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3188_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3188_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
v___jp_3175_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_unsigned_to_nat(1u);
v___x_3178_ = lean_nat_add(v_a_3168_, v___x_3177_);
lean_dec(v_a_3168_);
v_a_3168_ = v___x_3178_;
v_b_3169_ = v_a_3176_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___boxed(lean_object* v_upperBound_3227_, lean_object* v___x_3228_, lean_object* v___x_3229_, lean_object* v_xs_3230_, lean_object* v_a_3231_, lean_object* v_b_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v_upperBound_3227_, v___x_3228_, v___x_3229_, v_xs_3230_, v_a_3231_, v_b_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec_ref(v_xs_3230_);
lean_dec_ref(v___x_3229_);
lean_dec(v___x_3228_);
lean_dec(v_upperBound_3227_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0(lean_object* v_a_3239_, uint8_t v_induction_3240_, lean_object* v_elimName_3241_, lean_object* v_xs_3242_, lean_object* v_x_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_targetsPos_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_targetsPos_3249_ = lean_ctor_get(v_a_3239_, 3);
v___x_3250_ = lean_array_get_size(v_targetsPos_3249_);
v___x_3251_ = lean_unsigned_to_nat(0u);
v___x_3252_ = ((lean_object*)(l_Lean_Meta_addImplicitTargets___closed__0));
v___x_3253_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v___x_3250_, v___x_3250_, v_targetsPos_3249_, v_xs_3242_, v___x_3251_, v___x_3252_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3262_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3262_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3262_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3258_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3258_, 0, v_a_3254_);
lean_ctor_set(v___x_3258_, 1, v_elimName_3241_);
lean_ctor_set_uint8(v___x_3258_, sizeof(void*)*2, v_induction_3240_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3258_);
v___x_3260_ = v___x_3256_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec(v_elimName_3241_);
v_a_3263_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3253_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3253_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0___boxed(lean_object* v_a_3271_, lean_object* v_induction_3272_, lean_object* v_elimName_3273_, lean_object* v_xs_3274_, lean_object* v_x_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
uint8_t v_induction_boxed_3281_; lean_object* v_res_3282_; 
v_induction_boxed_3281_ = lean_unbox(v_induction_3272_);
v_res_3282_ = l_Lean_Meta_mkCustomEliminator___lam__0(v_a_3271_, v_induction_boxed_3281_, v_elimName_3273_, v_xs_3274_, v_x_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_x_3275_);
lean_dec_ref(v_xs_3274_);
lean_dec_ref(v_a_3271_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(lean_object* v_ref_3283_, lean_object* v_msg_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_fileName_3290_; lean_object* v_fileMap_3291_; lean_object* v_options_3292_; lean_object* v_currRecDepth_3293_; lean_object* v_maxRecDepth_3294_; lean_object* v_ref_3295_; lean_object* v_currNamespace_3296_; lean_object* v_openDecls_3297_; lean_object* v_initHeartbeats_3298_; lean_object* v_maxHeartbeats_3299_; lean_object* v_quotContext_3300_; lean_object* v_currMacroScope_3301_; uint8_t v_diag_3302_; lean_object* v_cancelTk_x3f_3303_; uint8_t v_suppressElabErrors_3304_; lean_object* v_inheritedTraceOptions_3305_; lean_object* v_ref_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_fileName_3290_ = lean_ctor_get(v___y_3287_, 0);
v_fileMap_3291_ = lean_ctor_get(v___y_3287_, 1);
v_options_3292_ = lean_ctor_get(v___y_3287_, 2);
v_currRecDepth_3293_ = lean_ctor_get(v___y_3287_, 3);
v_maxRecDepth_3294_ = lean_ctor_get(v___y_3287_, 4);
v_ref_3295_ = lean_ctor_get(v___y_3287_, 5);
v_currNamespace_3296_ = lean_ctor_get(v___y_3287_, 6);
v_openDecls_3297_ = lean_ctor_get(v___y_3287_, 7);
v_initHeartbeats_3298_ = lean_ctor_get(v___y_3287_, 8);
v_maxHeartbeats_3299_ = lean_ctor_get(v___y_3287_, 9);
v_quotContext_3300_ = lean_ctor_get(v___y_3287_, 10);
v_currMacroScope_3301_ = lean_ctor_get(v___y_3287_, 11);
v_diag_3302_ = lean_ctor_get_uint8(v___y_3287_, sizeof(void*)*14);
v_cancelTk_x3f_3303_ = lean_ctor_get(v___y_3287_, 12);
v_suppressElabErrors_3304_ = lean_ctor_get_uint8(v___y_3287_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3305_ = lean_ctor_get(v___y_3287_, 13);
v_ref_3306_ = l_Lean_replaceRef(v_ref_3283_, v_ref_3295_);
lean_inc_ref(v_inheritedTraceOptions_3305_);
lean_inc(v_cancelTk_x3f_3303_);
lean_inc(v_currMacroScope_3301_);
lean_inc(v_quotContext_3300_);
lean_inc(v_maxHeartbeats_3299_);
lean_inc(v_initHeartbeats_3298_);
lean_inc(v_openDecls_3297_);
lean_inc(v_currNamespace_3296_);
lean_inc(v_maxRecDepth_3294_);
lean_inc(v_currRecDepth_3293_);
lean_inc_ref(v_options_3292_);
lean_inc_ref(v_fileMap_3291_);
lean_inc_ref(v_fileName_3290_);
v___x_3307_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3307_, 0, v_fileName_3290_);
lean_ctor_set(v___x_3307_, 1, v_fileMap_3291_);
lean_ctor_set(v___x_3307_, 2, v_options_3292_);
lean_ctor_set(v___x_3307_, 3, v_currRecDepth_3293_);
lean_ctor_set(v___x_3307_, 4, v_maxRecDepth_3294_);
lean_ctor_set(v___x_3307_, 5, v_ref_3306_);
lean_ctor_set(v___x_3307_, 6, v_currNamespace_3296_);
lean_ctor_set(v___x_3307_, 7, v_openDecls_3297_);
lean_ctor_set(v___x_3307_, 8, v_initHeartbeats_3298_);
lean_ctor_set(v___x_3307_, 9, v_maxHeartbeats_3299_);
lean_ctor_set(v___x_3307_, 10, v_quotContext_3300_);
lean_ctor_set(v___x_3307_, 11, v_currMacroScope_3301_);
lean_ctor_set(v___x_3307_, 12, v_cancelTk_x3f_3303_);
lean_ctor_set(v___x_3307_, 13, v_inheritedTraceOptions_3305_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*14, v_diag_3302_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*14 + 1, v_suppressElabErrors_3304_);
v___x_3308_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_3284_, v___y_3285_, v___y_3286_, v___x_3307_, v___y_3288_);
lean_dec_ref_known(v___x_3307_, 14);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3309_, lean_object* v_msg_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3309_, v_msg_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v_ref_3309_);
return v_res_3316_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3317_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3321_ = lean_unsigned_to_nat(0u);
v___x_3322_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
lean_ctor_set(v___x_3322_, 2, v___x_3321_);
lean_ctor_set(v___x_3322_, 3, v___x_3321_);
lean_ctor_set(v___x_3322_, 4, v___x_3320_);
lean_ctor_set(v___x_3322_, 5, v___x_3320_);
lean_ctor_set(v___x_3322_, 6, v___x_3320_);
lean_ctor_set(v___x_3322_, 7, v___x_3320_);
lean_ctor_set(v___x_3322_, 8, v___x_3320_);
lean_ctor_set(v___x_3322_, 9, v___x_3320_);
lean_ctor_set(v___x_3322_, 10, v___x_3320_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_unsigned_to_nat(32u);
v___x_3324_ = lean_mk_empty_array_with_capacity(v___x_3323_);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3326_ = ((size_t)5ULL);
v___x_3327_ = lean_unsigned_to_nat(0u);
v___x_3328_ = lean_unsigned_to_nat(32u);
v___x_3329_ = lean_mk_empty_array_with_capacity(v___x_3328_);
v___x_3330_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3331_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v___x_3329_);
lean_ctor_set(v___x_3331_, 2, v___x_3327_);
lean_ctor_set(v___x_3331_, 3, v___x_3327_);
lean_ctor_set_usize(v___x_3331_, 4, v___x_3326_);
return v___x_3331_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3332_ = lean_box(1);
v___x_3333_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_3334_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
lean_ctor_set(v___x_3335_, 1, v___x_3333_);
lean_ctor_set(v___x_3335_, 2, v___x_3332_);
return v___x_3335_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_3338_ = l_Lean_stringToMessageData(v___x_3337_);
return v___x_3338_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_3341_ = l_Lean_stringToMessageData(v___x_3340_);
return v___x_3341_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_3344_ = l_Lean_stringToMessageData(v___x_3343_);
return v___x_3344_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_3347_ = l_Lean_stringToMessageData(v___x_3346_);
return v___x_3347_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_3350_ = l_Lean_stringToMessageData(v___x_3349_);
return v___x_3350_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_3353_ = l_Lean_stringToMessageData(v___x_3352_);
return v___x_3353_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_3356_ = l_Lean_stringToMessageData(v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3357_, lean_object* v_declHint_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; lean_object* v_env_3362_; uint8_t v___x_3363_; 
v___x_3361_ = lean_st_ref_get(v___y_3359_);
v_env_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc_ref(v_env_3362_);
lean_dec(v___x_3361_);
v___x_3363_ = l_Lean_Name_isAnonymous(v_declHint_3358_);
if (v___x_3363_ == 0)
{
uint8_t v_isExporting_3364_; 
v_isExporting_3364_ = lean_ctor_get_uint8(v_env_3362_, sizeof(void*)*8);
if (v_isExporting_3364_ == 0)
{
lean_object* v___x_3365_; 
lean_dec_ref(v_env_3362_);
lean_dec(v_declHint_3358_);
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v_msg_3357_);
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; uint8_t v___x_3367_; 
lean_inc_ref(v_env_3362_);
v___x_3366_ = l_Lean_Environment_setExporting(v_env_3362_, v___x_3363_);
lean_inc(v_declHint_3358_);
lean_inc_ref(v___x_3366_);
v___x_3367_ = l_Lean_Environment_contains(v___x_3366_, v_declHint_3358_, v_isExporting_3364_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
lean_dec_ref(v___x_3366_);
lean_dec_ref(v_env_3362_);
lean_dec(v_declHint_3358_);
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v_msg_3357_);
return v___x_3368_;
}
else
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v_c_3374_; lean_object* v___x_3375_; 
v___x_3369_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_3370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_3371_ = l_Lean_Options_empty;
v___x_3372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3366_);
lean_ctor_set(v___x_3372_, 1, v___x_3369_);
lean_ctor_set(v___x_3372_, 2, v___x_3370_);
lean_ctor_set(v___x_3372_, 3, v___x_3371_);
lean_inc(v_declHint_3358_);
v___x_3373_ = l_Lean_MessageData_ofConstName(v_declHint_3358_, v___x_3363_);
v_c_3374_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3374_, 0, v___x_3372_);
lean_ctor_set(v_c_3374_, 1, v___x_3373_);
v___x_3375_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3362_, v_declHint_3358_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_dec_ref(v_env_3362_);
lean_dec(v_declHint_3358_);
v___x_3376_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set(v___x_3377_, 1, v_c_3374_);
v___x_3378_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_3379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3377_);
lean_ctor_set(v___x_3379_, 1, v___x_3378_);
v___x_3380_ = l_Lean_MessageData_note(v___x_3379_);
v___x_3381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3381_, 0, v_msg_3357_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
return v___x_3382_;
}
else
{
lean_object* v_val_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3418_; 
v_val_3383_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3385_ = v___x_3375_;
v_isShared_3386_ = v_isSharedCheck_3418_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_val_3383_);
lean_dec(v___x_3375_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3418_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v_mod_3390_; uint8_t v___x_3391_; 
v___x_3387_ = lean_box(0);
v___x_3388_ = l_Lean_Environment_header(v_env_3362_);
lean_dec_ref(v_env_3362_);
v___x_3389_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3388_);
v_mod_3390_ = lean_array_get(v___x_3387_, v___x_3389_, v_val_3383_);
lean_dec(v_val_3383_);
lean_dec_ref(v___x_3389_);
v___x_3391_ = l_Lean_isPrivateName(v_declHint_3358_);
lean_dec(v_declHint_3358_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3392_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_3393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v_c_3374_);
v___x_3394_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_3395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = l_Lean_MessageData_ofName(v_mod_3390_);
v___x_3397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3395_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
v___x_3398_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = l_Lean_MessageData_note(v___x_3399_);
v___x_3401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3401_, 0, v_msg_3357_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set_tag(v___x_3385_, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3401_);
v___x_3403_ = v___x_3385_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3405_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v_c_3374_);
v___x_3407_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_3408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3406_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = l_Lean_MessageData_ofName(v_mod_3390_);
v___x_3410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3408_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_3412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3410_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = l_Lean_MessageData_note(v___x_3412_);
v___x_3414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3414_, 0, v_msg_3357_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set_tag(v___x_3385_, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3414_);
v___x_3416_ = v___x_3385_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3419_; 
lean_dec_ref(v_env_3362_);
lean_dec(v_declHint_3358_);
v___x_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3419_, 0, v_msg_3357_);
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3420_, lean_object* v_declHint_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3420_, v_declHint_3421_, v___y_3422_);
lean_dec(v___y_3422_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_3425_, lean_object* v_declHint_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v___x_3432_; lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3442_; 
v___x_3432_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3425_, v_declHint_3426_, v___y_3430_);
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3442_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3442_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3437_ = l_Lean_unknownIdentifierMessageTag;
v___x_3438_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
lean_ctor_set(v___x_3438_, 1, v_a_3433_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3438_);
v___x_3440_ = v___x_3435_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_3443_, lean_object* v_declHint_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_3443_, v_declHint_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_ref_3451_, lean_object* v_msg_3452_, lean_object* v_declHint_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3459_; lean_object* v_a_3460_; lean_object* v___x_3461_; 
v___x_3459_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_3452_, v_declHint_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref(v___x_3459_);
v___x_3461_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3451_, v_a_3460_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_ref_3462_, lean_object* v_msg_3463_, lean_object* v_declHint_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3462_, v_msg_3463_, v_declHint_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v_ref_3462_);
return v_res_3470_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0));
v___x_3473_ = l_Lean_stringToMessageData(v___x_3472_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_3474_, lean_object* v_constName_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v___x_3481_; uint8_t v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3481_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_3482_ = 0;
lean_inc(v_constName_3475_);
v___x_3483_ = l_Lean_MessageData_ofConstName(v_constName_3475_, v___x_3482_);
v___x_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3481_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3484_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3474_, v___x_3486_, v_constName_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_3488_, lean_object* v_constName_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3488_, v_constName_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v_ref_3488_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(lean_object* v_constName_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_ref_3502_; lean_object* v___x_3503_; 
v_ref_3502_ = lean_ctor_get(v___y_3499_, 5);
v___x_3503_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3502_, v_constName_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg___boxed(lean_object* v_constName_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(lean_object* v_constName_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v_env_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; 
v___x_3517_ = lean_st_ref_get(v___y_3515_);
v_env_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc_ref(v_env_3518_);
lean_dec(v___x_3517_);
v___x_3519_ = 0;
lean_inc(v_constName_3511_);
v___x_3520_ = l_Lean_Environment_find_x3f(v_env_3518_, v_constName_3511_, v___x_3519_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
return v___x_3521_;
}
else
{
lean_object* v_val_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v_constName_3511_);
v_val_3522_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3520_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_val_3522_);
lean_dec(v___x_3520_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set_tag(v___x_3524_, 0);
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_val_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3___boxed(lean_object* v_constName_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(v_constName_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator(lean_object* v_elimName_3537_, uint8_t v_induction_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = lean_box(0);
lean_inc(v_elimName_3537_);
v___x_3545_ = l_Lean_Meta_getElimInfo(v_elimName_3537_, v___x_3544_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
lean_inc(v_elimName_3537_);
v___x_3547_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(v_elimName_3537_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3549_; lean_object* v___f_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; lean_object* v___x_3553_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v___x_3549_ = lean_box(v_induction_3538_);
v___f_3550_ = lean_alloc_closure((void*)(l_Lean_Meta_mkCustomEliminator___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3550_, 0, v_a_3546_);
lean_closure_set(v___f_3550_, 1, v___x_3549_);
lean_closure_set(v___f_3550_, 2, v_elimName_3537_);
v___x_3551_ = l_Lean_ConstantInfo_type(v_a_3548_);
lean_dec(v_a_3548_);
v___x_3552_ = 0;
v___x_3553_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v___x_3551_, v___f_3550_, v___x_3552_, v___x_3552_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
return v___x_3553_;
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v_a_3546_);
lean_dec(v_elimName_3537_);
v_a_3554_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3547_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3547_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v_elimName_3537_);
v_a_3562_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3545_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3545_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___boxed(lean_object* v_elimName_3570_, lean_object* v_induction_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
uint8_t v_induction_boxed_3577_; lean_object* v_res_3578_; 
v_induction_boxed_3577_ = lean_unbox(v_induction_3571_);
v_res_3578_ = l_Lean_Meta_mkCustomEliminator(v_elimName_3570_, v_induction_boxed_3577_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(lean_object* v_upperBound_3579_, lean_object* v___x_3580_, lean_object* v_xs_3581_, lean_object* v___x_3582_, lean_object* v_inst_3583_, lean_object* v_R_3584_, lean_object* v_a_3585_, lean_object* v_b_3586_, lean_object* v_c_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v_upperBound_3579_, v___x_3580_, v_xs_3581_, v___x_3582_, v_a_3585_, v_b_3586_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___boxed(lean_object* v_upperBound_3594_, lean_object* v___x_3595_, lean_object* v_xs_3596_, lean_object* v___x_3597_, lean_object* v_inst_3598_, lean_object* v_R_3599_, lean_object* v_a_3600_, lean_object* v_b_3601_, lean_object* v_c_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(v_upperBound_3594_, v___x_3595_, v_xs_3596_, v___x_3597_, v_inst_3598_, v_R_3599_, v_a_3600_, v_b_3601_, v_c_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v___x_3597_);
lean_dec_ref(v_xs_3596_);
lean_dec_ref(v___x_3595_);
lean_dec(v_upperBound_3594_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(lean_object* v_upperBound_3609_, lean_object* v___x_3610_, lean_object* v___x_3611_, lean_object* v_xs_3612_, lean_object* v_inst_3613_, lean_object* v_R_3614_, lean_object* v_a_3615_, lean_object* v_b_3616_, lean_object* v_c_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v_upperBound_3609_, v___x_3610_, v___x_3611_, v_xs_3612_, v_a_3615_, v_b_3616_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___boxed(lean_object* v_upperBound_3624_, lean_object* v___x_3625_, lean_object* v___x_3626_, lean_object* v_xs_3627_, lean_object* v_inst_3628_, lean_object* v_R_3629_, lean_object* v_a_3630_, lean_object* v_b_3631_, lean_object* v_c_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(v_upperBound_3624_, v___x_3625_, v___x_3626_, v_xs_3627_, v_inst_3628_, v_R_3629_, v_a_3630_, v_b_3631_, v_c_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v_xs_3627_);
lean_dec_ref(v___x_3626_);
lean_dec(v___x_3625_);
lean_dec(v_upperBound_3624_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(lean_object* v_00_u03b1_3639_, lean_object* v_constName_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___boxed(lean_object* v_00_u03b1_3647_, lean_object* v_constName_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(v_00_u03b1_3647_, v_constName_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_3655_, lean_object* v_ref_3656_, lean_object* v_constName_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3656_, v_constName_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3664_, lean_object* v_ref_3665_, lean_object* v_constName_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(v_00_u03b1_3664_, v_ref_3665_, v_constName_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v_ref_3665_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3673_, lean_object* v_ref_3674_, lean_object* v_msg_3675_, lean_object* v_declHint_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3674_, v_msg_3675_, v_declHint_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3683_, lean_object* v_ref_3684_, lean_object* v_msg_3685_, lean_object* v_declHint_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3683_, v_ref_3684_, v_msg_3685_, v_declHint_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v_ref_3684_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(lean_object* v_msg_3693_, lean_object* v_declHint_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3693_, v_declHint_3694_, v___y_3698_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_3701_, lean_object* v_declHint_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(v_msg_3701_, v_declHint_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(lean_object* v_00_u03b1_3709_, lean_object* v_ref_3710_, lean_object* v_msg_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v___x_3717_; 
v___x_3717_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3710_, v_msg_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3718_, lean_object* v_ref_3719_, lean_object* v_msg_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(v_00_u03b1_3718_, v_ref_3719_, v_msg_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v_ref_3719_);
return v_res_3726_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3727_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0);
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
return v___x_3729_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
return v___x_3731_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
v___x_3733_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
lean_ctor_set(v___x_3733_, 2, v___x_3732_);
lean_ctor_set(v___x_3733_, 3, v___x_3732_);
lean_ctor_set(v___x_3733_, 4, v___x_3732_);
lean_ctor_set(v___x_3733_, 5, v___x_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(lean_object* v_ext_3734_, lean_object* v_b_3735_, uint8_t v_kind_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_currNamespace_3741_; lean_object* v___x_3742_; lean_object* v_env_3743_; lean_object* v_nextMacroScope_3744_; lean_object* v_ngen_3745_; lean_object* v_auxDeclNGen_3746_; lean_object* v_traceState_3747_; lean_object* v_messages_3748_; lean_object* v_infoState_3749_; lean_object* v_snapshotTasks_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3777_; 
v_currNamespace_3741_ = lean_ctor_get(v___y_3738_, 6);
v___x_3742_ = lean_st_ref_take(v___y_3739_);
v_env_3743_ = lean_ctor_get(v___x_3742_, 0);
v_nextMacroScope_3744_ = lean_ctor_get(v___x_3742_, 1);
v_ngen_3745_ = lean_ctor_get(v___x_3742_, 2);
v_auxDeclNGen_3746_ = lean_ctor_get(v___x_3742_, 3);
v_traceState_3747_ = lean_ctor_get(v___x_3742_, 4);
v_messages_3748_ = lean_ctor_get(v___x_3742_, 6);
v_infoState_3749_ = lean_ctor_get(v___x_3742_, 7);
v_snapshotTasks_3750_ = lean_ctor_get(v___x_3742_, 8);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3777_ == 0)
{
lean_object* v_unused_3778_; 
v_unused_3778_ = lean_ctor_get(v___x_3742_, 5);
lean_dec(v_unused_3778_);
v___x_3752_ = v___x_3742_;
v_isShared_3753_ = v_isSharedCheck_3777_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_snapshotTasks_3750_);
lean_inc(v_infoState_3749_);
lean_inc(v_messages_3748_);
lean_inc(v_traceState_3747_);
lean_inc(v_auxDeclNGen_3746_);
lean_inc(v_ngen_3745_);
lean_inc(v_nextMacroScope_3744_);
lean_inc(v_env_3743_);
lean_dec(v___x_3742_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3777_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3757_; 
lean_inc(v_currNamespace_3741_);
v___x_3754_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3743_, v_ext_3734_, v_b_3735_, v_kind_3736_, v_currNamespace_3741_);
v___x_3755_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 5, v___x_3755_);
lean_ctor_set(v___x_3752_, 0, v___x_3754_);
v___x_3757_ = v___x_3752_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_nextMacroScope_3744_);
lean_ctor_set(v_reuseFailAlloc_3776_, 2, v_ngen_3745_);
lean_ctor_set(v_reuseFailAlloc_3776_, 3, v_auxDeclNGen_3746_);
lean_ctor_set(v_reuseFailAlloc_3776_, 4, v_traceState_3747_);
lean_ctor_set(v_reuseFailAlloc_3776_, 5, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3776_, 6, v_messages_3748_);
lean_ctor_set(v_reuseFailAlloc_3776_, 7, v_infoState_3749_);
lean_ctor_set(v_reuseFailAlloc_3776_, 8, v_snapshotTasks_3750_);
v___x_3757_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v_mctx_3760_; lean_object* v_zetaDeltaFVarIds_3761_; lean_object* v_postponed_3762_; lean_object* v_diag_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3774_; 
v___x_3758_ = lean_st_ref_put(v___y_3739_, v___x_3757_);
v___x_3759_ = lean_st_ref_take(v___y_3737_);
v_mctx_3760_ = lean_ctor_get(v___x_3759_, 0);
v_zetaDeltaFVarIds_3761_ = lean_ctor_get(v___x_3759_, 2);
v_postponed_3762_ = lean_ctor_get(v___x_3759_, 3);
v_diag_3763_ = lean_ctor_get(v___x_3759_, 4);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3774_ == 0)
{
lean_object* v_unused_3775_; 
v_unused_3775_ = lean_ctor_get(v___x_3759_, 1);
lean_dec(v_unused_3775_);
v___x_3765_ = v___x_3759_;
v_isShared_3766_ = v_isSharedCheck_3774_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_diag_3763_);
lean_inc(v_postponed_3762_);
lean_inc(v_zetaDeltaFVarIds_3761_);
lean_inc(v_mctx_3760_);
lean_dec(v___x_3759_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3774_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3767_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 1, v___x_3767_);
v___x_3769_ = v___x_3765_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_mctx_3760_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v___x_3767_);
lean_ctor_set(v_reuseFailAlloc_3773_, 2, v_zetaDeltaFVarIds_3761_);
lean_ctor_set(v_reuseFailAlloc_3773_, 3, v_postponed_3762_);
lean_ctor_set(v_reuseFailAlloc_3773_, 4, v_diag_3763_);
v___x_3769_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3770_ = lean_st_ref_put(v___y_3737_, v___x_3769_);
v___x_3771_ = lean_box(0);
v___x_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
return v___x_3772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___boxed(lean_object* v_ext_3779_, lean_object* v_b_3780_, lean_object* v_kind_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
uint8_t v_kind_boxed_3786_; lean_object* v_res_3787_; 
v_kind_boxed_3786_ = lean_unbox(v_kind_3781_);
v_res_3787_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v_ext_3779_, v_b_3780_, v_kind_boxed_3786_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(lean_object* v_00_u03b1_3788_, lean_object* v_00_u03b2_3789_, lean_object* v_00_u03c3_3790_, lean_object* v_ext_3791_, lean_object* v_b_3792_, uint8_t v_kind_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v_ext_3791_, v_b_3792_, v_kind_3793_, v___y_3795_, v___y_3796_, v___y_3797_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___boxed(lean_object* v_00_u03b1_3800_, lean_object* v_00_u03b2_3801_, lean_object* v_00_u03c3_3802_, lean_object* v_ext_3803_, lean_object* v_b_3804_, lean_object* v_kind_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
uint8_t v_kind_boxed_3811_; lean_object* v_res_3812_; 
v_kind_boxed_3811_ = lean_unbox(v_kind_3805_);
v_res_3812_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(v_00_u03b1_3800_, v_00_u03b2_3801_, v_00_u03c3_3802_, v_ext_3803_, v_b_3804_, v_kind_boxed_3811_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator(lean_object* v_declName_3813_, uint8_t v_attrKind_3814_, uint8_t v_induction_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_Meta_mkCustomEliminator(v_declName_3813_, v_induction_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3821_, 1);
v___x_3823_ = l_Lean_Meta_customEliminatorExt;
v___x_3824_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v___x_3823_, v_a_3822_, v_attrKind_3814_, v_a_3817_, v_a_3818_, v_a_3819_);
return v___x_3824_;
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3821_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3821_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator___boxed(lean_object* v_declName_3833_, lean_object* v_attrKind_3834_, lean_object* v_induction_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_){
_start:
{
uint8_t v_attrKind_boxed_3841_; uint8_t v_induction_boxed_3842_; lean_object* v_res_3843_; 
v_attrKind_boxed_3841_ = lean_unbox(v_attrKind_3834_);
v_induction_boxed_3842_ = lean_unbox(v_induction_3835_);
v_res_3843_ = l_Lean_Meta_addCustomEliminator(v_declName_3833_, v_attrKind_boxed_3841_, v_induction_boxed_3842_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
return v_res_3843_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3850_; uint64_t v___x_3851_; 
v___x_3850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3851_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3850_);
return v___x_3851_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3852_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3854_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
lean_ctor_set_uint64(v___x_3854_, sizeof(void*)*1, v___x_3852_);
return v___x_3854_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3855_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
return v___x_3857_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3859_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
lean_ctor_set(v___x_3859_, 2, v___x_3858_);
lean_ctor_set(v___x_3859_, 3, v___x_3858_);
lean_ctor_set(v___x_3859_, 4, v___x_3858_);
lean_ctor_set(v___x_3859_, 5, v___x_3858_);
return v___x_3859_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
lean_ctor_set(v___x_3861_, 2, v___x_3860_);
lean_ctor_set(v___x_3861_, 3, v___x_3860_);
lean_ctor_set(v___x_3861_, 4, v___x_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object* v___x_3862_, lean_object* v___x_3863_, lean_object* v_declName_3864_, lean_object* v_x_3865_, uint8_t v_attrKind_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
uint8_t v___x_3870_; uint8_t v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; size_t v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3870_ = 1;
v___x_3871_ = 0;
v___x_3872_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3873_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3874_ = lean_unsigned_to_nat(32u);
v___x_3875_ = lean_mk_empty_array_with_capacity(v___x_3874_);
v___x_3876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3877_ = ((size_t)5ULL);
lean_inc_n(v___x_3862_, 6);
v___x_3878_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3878_, 0, v___x_3876_);
lean_ctor_set(v___x_3878_, 1, v___x_3875_);
lean_ctor_set(v___x_3878_, 2, v___x_3862_);
lean_ctor_set(v___x_3878_, 3, v___x_3862_);
lean_ctor_set_usize(v___x_3878_, 4, v___x_3877_);
v___x_3879_ = lean_box(1);
lean_inc_ref(v___x_3878_);
v___x_3880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3873_);
lean_ctor_set(v___x_3880_, 1, v___x_3878_);
lean_ctor_set(v___x_3880_, 2, v___x_3879_);
v___x_3881_ = lean_mk_empty_array_with_capacity(v___x_3862_);
v___x_3882_ = lean_box(0);
lean_inc(v___x_3863_);
v___x_3883_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3883_, 0, v___x_3872_);
lean_ctor_set(v___x_3883_, 1, v___x_3863_);
lean_ctor_set(v___x_3883_, 2, v___x_3880_);
lean_ctor_set(v___x_3883_, 3, v___x_3881_);
lean_ctor_set(v___x_3883_, 4, v___x_3882_);
lean_ctor_set(v___x_3883_, 5, v___x_3862_);
lean_ctor_set(v___x_3883_, 6, v___x_3882_);
lean_ctor_set_uint8(v___x_3883_, sizeof(void*)*7, v___x_3871_);
lean_ctor_set_uint8(v___x_3883_, sizeof(void*)*7 + 1, v___x_3871_);
lean_ctor_set_uint8(v___x_3883_, sizeof(void*)*7 + 2, v___x_3871_);
lean_ctor_set_uint8(v___x_3883_, sizeof(void*)*7 + 3, v___x_3870_);
v___x_3884_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3862_);
lean_ctor_set(v___x_3884_, 1, v___x_3862_);
lean_ctor_set(v___x_3884_, 2, v___x_3862_);
lean_ctor_set(v___x_3884_, 3, v___x_3862_);
lean_ctor_set(v___x_3884_, 4, v___x_3873_);
lean_ctor_set(v___x_3884_, 5, v___x_3873_);
lean_ctor_set(v___x_3884_, 6, v___x_3873_);
lean_ctor_set(v___x_3884_, 7, v___x_3873_);
lean_ctor_set(v___x_3884_, 8, v___x_3873_);
lean_ctor_set(v___x_3884_, 9, v___x_3873_);
lean_ctor_set(v___x_3884_, 10, v___x_3873_);
v___x_3885_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3886_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3884_);
lean_ctor_set(v___x_3887_, 1, v___x_3885_);
lean_ctor_set(v___x_3887_, 2, v___x_3863_);
lean_ctor_set(v___x_3887_, 3, v___x_3878_);
lean_ctor_set(v___x_3887_, 4, v___x_3886_);
v___x_3888_ = lean_st_mk_ref(v___x_3887_);
v___x_3889_ = l_Lean_Meta_addCustomEliminator(v_declName_3864_, v_attrKind_3866_, v___x_3870_, v___x_3883_, v___x_3888_, v___y_3867_, v___y_3868_);
lean_dec_ref_known(v___x_3883_, 7);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3898_; 
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3898_ == 0)
{
lean_object* v_unused_3899_; 
v_unused_3899_ = lean_ctor_get(v___x_3889_, 0);
lean_dec(v_unused_3899_);
v___x_3891_ = v___x_3889_;
v_isShared_3892_ = v_isSharedCheck_3898_;
goto v_resetjp_3890_;
}
else
{
lean_dec(v___x_3889_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3898_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3893_ = lean_st_ref_get(v___x_3888_);
lean_dec(v___x_3888_);
lean_dec(v___x_3893_);
v___x_3894_ = lean_box(0);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 0, v___x_3894_);
v___x_3896_ = v___x_3891_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
else
{
lean_dec(v___x_3888_);
return v___x_3889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v___x_3900_, lean_object* v___x_3901_, lean_object* v_declName_3902_, lean_object* v_x_3903_, lean_object* v_attrKind_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
uint8_t v_attrKind_boxed_3908_; lean_object* v_res_3909_; 
v_attrKind_boxed_3908_ = lean_unbox(v_attrKind_3904_);
v_res_3909_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_3900_, v___x_3901_, v_declName_3902_, v_x_3903_, v_attrKind_boxed_3908_, v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v_x_3903_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v___x_3914_; lean_object* v_env_3915_; lean_object* v_options_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3914_ = lean_st_ref_get(v___y_3912_);
v_env_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc_ref(v_env_3915_);
lean_dec(v___x_3914_);
v_options_3916_ = lean_ctor_get(v___y_3911_, 2);
v___x_3917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_3918_ = lean_unsigned_to_nat(32u);
v___x_3919_ = lean_mk_empty_array_with_capacity(v___x_3918_);
lean_dec_ref(v___x_3919_);
v___x_3920_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
lean_inc_ref(v_options_3916_);
v___x_3921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3921_, 0, v_env_3915_);
lean_ctor_set(v___x_3921_, 1, v___x_3917_);
lean_ctor_set(v___x_3921_, 2, v___x_3920_);
lean_ctor_set(v___x_3921_, 3, v_options_3916_);
v___x_3922_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
lean_ctor_set(v___x_3922_, 1, v_msgData_3910_);
v___x_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3924_, v___y_3925_, v___y_3926_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v_ref_3933_; lean_object* v___x_3934_; lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3943_; 
v_ref_3933_ = lean_ctor_get(v___y_3930_, 5);
v___x_3934_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msg_3929_, v___y_3930_, v___y_3931_);
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_3943_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3943_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
lean_inc(v_ref_3933_);
v___x_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3939_, 0, v_ref_3933_);
lean_ctor_set(v___x_3939_, 1, v_a_3935_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set_tag(v___x_3937_, 1);
lean_ctor_set(v___x_3937_, 0, v___x_3939_);
v___x_3941_ = v___x_3937_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
return v_res_3948_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3951_ = l_Lean_stringToMessageData(v___x_3950_);
return v___x_3951_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3954_ = l_Lean_stringToMessageData(v___x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object* v___x_3955_, lean_object* v_decl_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3961_ = l_Lean_MessageData_ofName(v___x_3955_);
v___x_3962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3960_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3962_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
v___x_3965_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_3964_, v___y_3957_, v___y_3958_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v___x_3966_, lean_object* v_decl_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_3966_, v_decl_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v_decl_3967_);
return v_res_3971_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4022_ = lean_unsigned_to_nat(2729305610u);
v___x_4023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4024_ = l_Lean_Name_num___override(v___x_4023_, v___x_4022_);
return v___x_4024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4027_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4028_ = l_Lean_Name_str___override(v___x_4027_, v___x_4026_);
return v___x_4028_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4032_ = l_Lean_Name_str___override(v___x_4031_, v___x_4030_);
return v___x_4032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4033_ = lean_unsigned_to_nat(2u);
v___x_4034_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4035_ = l_Lean_Name_num___override(v___x_4034_, v___x_4033_);
return v___x_4035_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4042_ = 0;
v___x_4043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4045_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4046_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
lean_ctor_set(v___x_4046_, 1, v___x_4044_);
lean_ctor_set(v___x_4046_, 2, v___x_4043_);
lean_ctor_set_uint8(v___x_4046_, sizeof(void*)*3, v___x_4042_);
return v___x_4046_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4047_; lean_object* v___f_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___f_4047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___f_4048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4049_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
lean_ctor_set(v___x_4050_, 1, v___f_4048_);
lean_ctor_set(v___x_4050_, 2, v___f_4047_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4053_ = l_Lean_registerBuiltinAttribute(v___x_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v_a_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_4056_, lean_object* v_msg_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_4057_, v___y_4058_, v___y_4059_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_4062_, lean_object* v_msg_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(v_00_u03b1_4062_, v_msg_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4070_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4072_ = l_Lean_addBuiltinDocString(v___x_4070_, v___x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object* v___x_4075_, lean_object* v___x_4076_, lean_object* v_declName_4077_, lean_object* v_x_4078_, uint8_t v_attrKind_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
uint8_t v___x_4083_; uint8_t v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; size_t v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4083_ = 0;
v___x_4084_ = 1;
v___x_4085_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4087_ = lean_unsigned_to_nat(32u);
v___x_4088_ = lean_mk_empty_array_with_capacity(v___x_4087_);
v___x_4089_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_4090_ = ((size_t)5ULL);
lean_inc_n(v___x_4075_, 6);
v___x_4091_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4088_);
lean_ctor_set(v___x_4091_, 2, v___x_4075_);
lean_ctor_set(v___x_4091_, 3, v___x_4075_);
lean_ctor_set_usize(v___x_4091_, 4, v___x_4090_);
v___x_4092_ = lean_box(1);
lean_inc_ref(v___x_4091_);
v___x_4093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4086_);
lean_ctor_set(v___x_4093_, 1, v___x_4091_);
lean_ctor_set(v___x_4093_, 2, v___x_4092_);
v___x_4094_ = lean_mk_empty_array_with_capacity(v___x_4075_);
v___x_4095_ = lean_box(0);
lean_inc(v___x_4076_);
v___x_4096_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4096_, 0, v___x_4085_);
lean_ctor_set(v___x_4096_, 1, v___x_4076_);
lean_ctor_set(v___x_4096_, 2, v___x_4093_);
lean_ctor_set(v___x_4096_, 3, v___x_4094_);
lean_ctor_set(v___x_4096_, 4, v___x_4095_);
lean_ctor_set(v___x_4096_, 5, v___x_4075_);
lean_ctor_set(v___x_4096_, 6, v___x_4095_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*7, v___x_4083_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*7 + 1, v___x_4083_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*7 + 2, v___x_4083_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*7 + 3, v___x_4084_);
v___x_4097_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4075_);
lean_ctor_set(v___x_4097_, 1, v___x_4075_);
lean_ctor_set(v___x_4097_, 2, v___x_4075_);
lean_ctor_set(v___x_4097_, 3, v___x_4075_);
lean_ctor_set(v___x_4097_, 4, v___x_4086_);
lean_ctor_set(v___x_4097_, 5, v___x_4086_);
lean_ctor_set(v___x_4097_, 6, v___x_4086_);
lean_ctor_set(v___x_4097_, 7, v___x_4086_);
lean_ctor_set(v___x_4097_, 8, v___x_4086_);
lean_ctor_set(v___x_4097_, 9, v___x_4086_);
lean_ctor_set(v___x_4097_, 10, v___x_4086_);
v___x_4098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4099_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4097_);
lean_ctor_set(v___x_4100_, 1, v___x_4098_);
lean_ctor_set(v___x_4100_, 2, v___x_4076_);
lean_ctor_set(v___x_4100_, 3, v___x_4091_);
lean_ctor_set(v___x_4100_, 4, v___x_4099_);
v___x_4101_ = lean_st_mk_ref(v___x_4100_);
v___x_4102_ = l_Lean_Meta_addCustomEliminator(v_declName_4077_, v_attrKind_4079_, v___x_4083_, v___x_4096_, v___x_4101_, v___y_4080_, v___y_4081_);
lean_dec_ref_known(v___x_4096_, 7);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4111_; 
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4111_ == 0)
{
lean_object* v_unused_4112_; 
v_unused_4112_ = lean_ctor_get(v___x_4102_, 0);
lean_dec(v_unused_4112_);
v___x_4104_ = v___x_4102_;
v_isShared_4105_ = v_isSharedCheck_4111_;
goto v_resetjp_4103_;
}
else
{
lean_dec(v___x_4102_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4111_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4109_; 
v___x_4106_ = lean_st_ref_get(v___x_4101_);
lean_dec(v___x_4101_);
lean_dec(v___x_4106_);
v___x_4107_ = lean_box(0);
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 0, v___x_4107_);
v___x_4109_ = v___x_4104_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
else
{
lean_dec(v___x_4101_);
return v___x_4102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v___x_4113_, lean_object* v___x_4114_, lean_object* v_declName_4115_, lean_object* v_x_4116_, lean_object* v_attrKind_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
uint8_t v_attrKind_boxed_4121_; lean_object* v_res_4122_; 
v_attrKind_boxed_4121_ = lean_unbox(v_attrKind_4117_);
v_res_4122_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_4113_, v___x_4114_, v_declName_4115_, v_x_4116_, v_attrKind_boxed_4121_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v_x_4116_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object* v___x_4123_, lean_object* v_decl_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4129_ = l_Lean_MessageData_ofName(v___x_4123_);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4128_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4130_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_4132_, v___y_4125_, v___y_4126_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v___x_4134_, lean_object* v_decl_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_4134_, v_decl_4135_, v___y_4136_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v_decl_4135_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4172_ = l_Lean_registerBuiltinAttribute(v___x_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v_a_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4179_ = l_Lean_addBuiltinDocString(v___x_4177_, v___x_4178_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v_a_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg(lean_object* v_a_4182_){
_start:
{
lean_object* v___x_4184_; lean_object* v_env_4185_; lean_object* v___x_4186_; lean_object* v_ext_4187_; lean_object* v_toEnvExtension_4188_; lean_object* v_asyncMode_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4184_ = lean_st_ref_get(v_a_4182_);
v_env_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc_ref(v_env_4185_);
lean_dec(v___x_4184_);
v___x_4186_ = l_Lean_Meta_customEliminatorExt;
v_ext_4187_ = lean_ctor_get(v___x_4186_, 1);
v_toEnvExtension_4188_ = lean_ctor_get(v_ext_4187_, 0);
v_asyncMode_4189_ = lean_ctor_get(v_toEnvExtension_4188_, 2);
v___x_4190_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
v___x_4191_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4190_, v___x_4186_, v_env_4185_, v_asyncMode_4189_);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg___boxed(lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_4193_);
lean_dec(v_a_4193_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators(lean_object* v_a_4196_, lean_object* v_a_4197_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_4197_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___boxed(lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Lean_Meta_getCustomEliminators(v_a_4200_, v_a_4201_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_m_4204_, lean_object* v_query_4205_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_m_4204_, v_query_4205_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_index_4207_; lean_object* v_key_4208_; lean_object* v_value_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
v_index_4207_ = lean_ctor_get(v___x_4206_, 0);
v_key_4208_ = lean_ctor_get(v___x_4206_, 1);
v_value_4209_ = lean_ctor_get(v___x_4206_, 2);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4206_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_value_4209_);
lean_inc(v_key_4208_);
lean_inc(v_index_4207_);
lean_dec(v___x_4206_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_index_4207_);
lean_ctor_set(v_reuseFailAlloc_4215_, 1, v_key_4208_);
lean_ctor_set(v_reuseFailAlloc_4215_, 2, v_value_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
else
{
lean_object* v___x_4217_; 
lean_dec(v___x_4206_);
v___x_4217_ = lean_box(1);
return v___x_4217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_4218_, lean_object* v_query_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_m_4218_, v_query_4219_);
lean_dec_ref(v_query_4219_);
lean_dec_ref(v_m_4218_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(lean_object* v_m_4221_, lean_object* v_a_4222_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_m_4221_, v_a_4222_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_value_4224_; lean_object* v___x_4225_; 
v_value_4224_ = lean_ctor_get(v___x_4223_, 2);
lean_inc(v_value_4224_);
lean_dec_ref_known(v___x_4223_, 3);
v___x_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4225_, 0, v_value_4224_);
return v___x_4225_;
}
else
{
lean_object* v___x_4226_; 
v___x_4226_ = lean_box(0);
return v___x_4226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_m_4227_, lean_object* v_a_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_4227_, v_a_4228_);
lean_dec_ref(v_a_4228_);
lean_dec_ref(v_m_4227_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_4230_, lean_object* v_vals_4231_, lean_object* v_i_4232_, lean_object* v_k_4233_){
_start:
{
lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4238_ = lean_array_get_size(v_keys_4230_);
v___x_4239_ = lean_nat_dec_lt(v_i_4232_, v___x_4238_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; 
lean_dec(v_i_4232_);
v___x_4240_ = lean_box(0);
return v___x_4240_;
}
else
{
lean_object* v_fst_4241_; lean_object* v_snd_4242_; lean_object* v_k_x27_4243_; lean_object* v_fst_4244_; lean_object* v_snd_4245_; uint8_t v___y_4247_; uint8_t v___x_4254_; 
v_fst_4241_ = lean_ctor_get(v_k_4233_, 0);
v_snd_4242_ = lean_ctor_get(v_k_4233_, 1);
v_k_x27_4243_ = lean_array_fget_borrowed(v_keys_4230_, v_i_4232_);
v_fst_4244_ = lean_ctor_get(v_k_x27_4243_, 0);
v_snd_4245_ = lean_ctor_get(v_k_x27_4243_, 1);
v___x_4254_ = lean_unbox(v_fst_4241_);
if (v___x_4254_ == 0)
{
uint8_t v___x_4255_; 
v___x_4255_ = lean_unbox(v_fst_4244_);
if (v___x_4255_ == 0)
{
v___y_4247_ = v___x_4239_;
goto v___jp_4246_;
}
else
{
goto v___jp_4234_;
}
}
else
{
uint8_t v___x_4256_; 
v___x_4256_ = lean_unbox(v_fst_4244_);
v___y_4247_ = v___x_4256_;
goto v___jp_4246_;
}
v___jp_4246_:
{
if (v___y_4247_ == 0)
{
goto v___jp_4234_;
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4249_; uint8_t v___x_4250_; 
v___x_4248_ = lean_array_get_size(v_snd_4242_);
v___x_4249_ = lean_array_get_size(v_snd_4245_);
v___x_4250_ = lean_nat_dec_eq(v___x_4248_, v___x_4249_);
if (v___x_4250_ == 0)
{
goto v___jp_4234_;
}
else
{
uint8_t v___x_4251_; 
v___x_4251_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4242_, v_snd_4245_, v___x_4248_);
if (v___x_4251_ == 0)
{
goto v___jp_4234_;
}
else
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_array_fget_borrowed(v_vals_4231_, v_i_4232_);
lean_dec(v_i_4232_);
lean_inc(v___x_4252_);
v___x_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4252_);
return v___x_4253_;
}
}
}
}
}
v___jp_4234_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = lean_unsigned_to_nat(1u);
v___x_4236_ = lean_nat_add(v_i_4232_, v___x_4235_);
lean_dec(v_i_4232_);
v_i_4232_ = v___x_4236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_4257_, lean_object* v_vals_4258_, lean_object* v_i_4259_, lean_object* v_k_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_4257_, v_vals_4258_, v_i_4259_, v_k_4260_);
lean_dec_ref(v_k_4260_);
lean_dec_ref(v_vals_4258_);
lean_dec_ref(v_keys_4257_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_x_4262_, size_t v_x_4263_, lean_object* v_x_4264_){
_start:
{
if (lean_obj_tag(v_x_4262_) == 0)
{
lean_object* v_es_4265_; lean_object* v___x_4266_; size_t v___x_4267_; size_t v___x_4268_; lean_object* v_j_4269_; lean_object* v___x_4270_; 
v_es_4265_ = lean_ctor_get(v_x_4262_, 0);
v___x_4266_ = lean_box(2);
v___x_4267_ = ((size_t)31ULL);
v___x_4268_ = lean_usize_land(v_x_4263_, v___x_4267_);
v_j_4269_ = lean_usize_to_nat(v___x_4268_);
v___x_4270_ = lean_array_get_borrowed(v___x_4266_, v_es_4265_, v_j_4269_);
lean_dec(v_j_4269_);
switch(lean_obj_tag(v___x_4270_))
{
case 0:
{
lean_object* v_key_4271_; lean_object* v_val_4272_; lean_object* v_fst_4273_; lean_object* v_snd_4274_; lean_object* v_fst_4275_; lean_object* v_snd_4276_; uint8_t v___x_4285_; 
v_key_4271_ = lean_ctor_get(v___x_4270_, 0);
v_val_4272_ = lean_ctor_get(v___x_4270_, 1);
v_fst_4273_ = lean_ctor_get(v_x_4264_, 0);
v_snd_4274_ = lean_ctor_get(v_x_4264_, 1);
v_fst_4275_ = lean_ctor_get(v_key_4271_, 0);
v_snd_4276_ = lean_ctor_get(v_key_4271_, 1);
v___x_4285_ = lean_unbox(v_fst_4273_);
if (v___x_4285_ == 0)
{
uint8_t v___x_4286_; 
v___x_4286_ = lean_unbox(v_fst_4275_);
if (v___x_4286_ == 0)
{
goto v___jp_4277_;
}
else
{
lean_object* v___x_4287_; 
v___x_4287_ = lean_box(0);
return v___x_4287_;
}
}
else
{
uint8_t v___x_4288_; 
v___x_4288_ = lean_unbox(v_fst_4275_);
if (v___x_4288_ == 0)
{
lean_object* v___x_4289_; 
v___x_4289_ = lean_box(0);
return v___x_4289_;
}
else
{
goto v___jp_4277_;
}
}
v___jp_4277_:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; uint8_t v___x_4280_; 
v___x_4278_ = lean_array_get_size(v_snd_4274_);
v___x_4279_ = lean_array_get_size(v_snd_4276_);
v___x_4280_ = lean_nat_dec_eq(v___x_4278_, v___x_4279_);
if (v___x_4280_ == 0)
{
lean_object* v___x_4281_; 
v___x_4281_ = lean_box(0);
return v___x_4281_;
}
else
{
uint8_t v___x_4282_; 
v___x_4282_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4274_, v_snd_4276_, v___x_4278_);
if (v___x_4282_ == 0)
{
lean_object* v___x_4283_; 
v___x_4283_ = lean_box(0);
return v___x_4283_;
}
else
{
lean_object* v___x_4284_; 
lean_inc(v_val_4272_);
v___x_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4284_, 0, v_val_4272_);
return v___x_4284_;
}
}
}
}
case 1:
{
lean_object* v_node_4290_; size_t v___x_4291_; size_t v___x_4292_; 
v_node_4290_ = lean_ctor_get(v___x_4270_, 0);
v___x_4291_ = ((size_t)5ULL);
v___x_4292_ = lean_usize_shift_right(v_x_4263_, v___x_4291_);
v_x_4262_ = v_node_4290_;
v_x_4263_ = v___x_4292_;
goto _start;
}
default: 
{
lean_object* v___x_4294_; 
v___x_4294_ = lean_box(0);
return v___x_4294_;
}
}
}
else
{
lean_object* v_ks_4295_; lean_object* v_vs_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v_ks_4295_ = lean_ctor_get(v_x_4262_, 0);
v_vs_4296_ = lean_ctor_get(v_x_4262_, 1);
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_ks_4295_, v_vs_4296_, v___x_4297_, v_x_4264_);
return v___x_4298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_4299_, lean_object* v_x_4300_, lean_object* v_x_4301_){
_start:
{
size_t v_x_2020__boxed_4302_; lean_object* v_res_4303_; 
v_x_2020__boxed_4302_ = lean_unbox_usize(v_x_4300_);
lean_dec(v_x_4300_);
v_res_4303_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4299_, v_x_2020__boxed_4302_, v_x_4301_);
lean_dec_ref(v_x_4301_);
lean_dec_ref(v_x_4299_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(lean_object* v_x_4304_, lean_object* v_x_4305_){
_start:
{
uint64_t v___y_4307_; uint64_t v___y_4308_; lean_object* v_fst_4312_; lean_object* v_snd_4313_; uint64_t v___y_4315_; uint8_t v___x_4327_; 
v_fst_4312_ = lean_ctor_get(v_x_4305_, 0);
v_snd_4313_ = lean_ctor_get(v_x_4305_, 1);
v___x_4327_ = lean_unbox(v_fst_4312_);
if (v___x_4327_ == 0)
{
uint64_t v___x_4328_; 
v___x_4328_ = 13ULL;
v___y_4315_ = v___x_4328_;
goto v___jp_4314_;
}
else
{
uint64_t v___x_4329_; 
v___x_4329_ = 11ULL;
v___y_4315_ = v___x_4329_;
goto v___jp_4314_;
}
v___jp_4306_:
{
uint64_t v___x_4309_; size_t v___x_4310_; lean_object* v___x_4311_; 
v___x_4309_ = lean_uint64_mix_hash(v___y_4307_, v___y_4308_);
v___x_4310_ = lean_uint64_to_usize(v___x_4309_);
v___x_4311_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4304_, v___x_4310_, v_x_4305_);
return v___x_4311_;
}
v___jp_4314_:
{
uint64_t v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4316_ = 7ULL;
v___x_4317_ = lean_unsigned_to_nat(0u);
v___x_4318_ = lean_array_get_size(v_snd_4313_);
v___x_4319_ = lean_nat_dec_lt(v___x_4317_, v___x_4318_);
if (v___x_4319_ == 0)
{
v___y_4307_ = v___y_4315_;
v___y_4308_ = v___x_4316_;
goto v___jp_4306_;
}
else
{
uint8_t v___x_4320_; 
v___x_4320_ = lean_nat_dec_le(v___x_4318_, v___x_4318_);
if (v___x_4320_ == 0)
{
if (v___x_4319_ == 0)
{
v___y_4307_ = v___y_4315_;
v___y_4308_ = v___x_4316_;
goto v___jp_4306_;
}
else
{
size_t v___x_4321_; size_t v___x_4322_; uint64_t v___x_4323_; 
v___x_4321_ = ((size_t)0ULL);
v___x_4322_ = lean_usize_of_nat(v___x_4318_);
v___x_4323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4313_, v___x_4321_, v___x_4322_, v___x_4316_);
v___y_4307_ = v___y_4315_;
v___y_4308_ = v___x_4323_;
goto v___jp_4306_;
}
}
else
{
size_t v___x_4324_; size_t v___x_4325_; uint64_t v___x_4326_; 
v___x_4324_ = ((size_t)0ULL);
v___x_4325_ = lean_usize_of_nat(v___x_4318_);
v___x_4326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4313_, v___x_4324_, v___x_4325_, v___x_4316_);
v___y_4307_ = v___y_4315_;
v___y_4308_ = v___x_4326_;
goto v___jp_4306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_4330_, lean_object* v_x_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_4330_, v_x_4331_);
lean_dec_ref(v_x_4331_);
lean_dec_ref(v_x_4330_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(lean_object* v_x_4333_, lean_object* v_x_4334_){
_start:
{
uint8_t v_stage_u2081_4335_; 
v_stage_u2081_4335_ = lean_ctor_get_uint8(v_x_4333_, sizeof(void*)*2);
if (v_stage_u2081_4335_ == 0)
{
lean_object* v_map_u2081_4336_; lean_object* v_map_u2082_4337_; lean_object* v___x_4338_; 
v_map_u2081_4336_ = lean_ctor_get(v_x_4333_, 0);
v_map_u2082_4337_ = lean_ctor_get(v_x_4333_, 1);
v___x_4338_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_map_u2082_4337_, v_x_4334_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v___x_4339_; 
v___x_4339_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_4336_, v_x_4334_);
return v___x_4339_;
}
else
{
return v___x_4338_;
}
}
else
{
lean_object* v_map_u2081_4340_; lean_object* v___x_4341_; 
v_map_u2081_4340_ = lean_ctor_get(v_x_4333_, 0);
v___x_4341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_4340_, v_x_4334_);
return v___x_4341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg___boxed(lean_object* v_x_4342_, lean_object* v_x_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v_x_4342_, v_x_4343_);
lean_dec_ref(v_x_4343_);
lean_dec_ref(v_x_4342_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(lean_object* v_as_4347_, size_t v_sz_4348_, size_t v_i_4349_, lean_object* v_b_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
uint8_t v___x_4356_; 
v___x_4356_ = lean_usize_dec_lt(v_i_4349_, v_sz_4348_);
if (v___x_4356_ == 0)
{
lean_object* v___x_4357_; 
v___x_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4357_, 0, v_b_4350_);
return v___x_4357_;
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4359_; 
v_a_4358_ = lean_array_uget_borrowed(v_as_4347_, v_i_4349_);
lean_inc(v___y_4354_);
lean_inc_ref(v___y_4353_);
lean_inc(v___y_4352_);
lean_inc_ref(v___y_4351_);
lean_inc(v_a_4358_);
v___x_4359_ = lean_infer_type(v_a_4358_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4361_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4359_, 1);
v___x_4361_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_a_4360_, v___y_4352_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4390_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4364_ = v___x_4361_;
v_isShared_4365_ = v_isSharedCheck_4390_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4361_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4390_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v_snd_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4388_; 
v_snd_4366_ = lean_ctor_get(v_b_4350_, 1);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_b_4350_);
if (v_isSharedCheck_4388_ == 0)
{
lean_object* v_unused_4389_; 
v_unused_4389_ = lean_ctor_get(v_b_4350_, 0);
lean_dec(v_unused_4389_);
v___x_4368_ = v_b_4350_;
v_isShared_4369_ = v_isSharedCheck_4388_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_snd_4366_);
lean_dec(v_b_4350_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4388_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4370_ = l_Lean_Expr_headBeta(v_a_4362_);
v___x_4371_ = l_Lean_Expr_getAppFn(v___x_4370_);
lean_dec_ref(v___x_4370_);
if (lean_obj_tag(v___x_4371_) == 4)
{
lean_object* v_declName_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4376_; 
lean_del_object(v___x_4364_);
v_declName_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_declName_4372_);
lean_dec_ref_known(v___x_4371_, 2);
v___x_4373_ = lean_box(0);
v___x_4374_ = lean_array_push(v_snd_4366_, v_declName_4372_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 1, v___x_4374_);
lean_ctor_set(v___x_4368_, 0, v___x_4373_);
v___x_4376_ = v___x_4368_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4373_);
lean_ctor_set(v_reuseFailAlloc_4380_, 1, v___x_4374_);
v___x_4376_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
size_t v___x_4377_; size_t v___x_4378_; 
v___x_4377_ = ((size_t)1ULL);
v___x_4378_ = lean_usize_add(v_i_4349_, v___x_4377_);
v_i_4349_ = v___x_4378_;
v_b_4350_ = v___x_4376_;
goto _start;
}
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4383_; 
lean_dec_ref(v___x_4371_);
v___x_4381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0));
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 0, v___x_4381_);
v___x_4383_ = v___x_4368_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4381_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_snd_4366_);
v___x_4383_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
lean_object* v___x_4385_; 
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 0, v___x_4383_);
v___x_4385_ = v___x_4364_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_dec_ref(v_b_4350_);
v_a_4391_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4361_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4361_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
lean_dec_ref(v_b_4350_);
v_a_4399_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4359_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4359_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___boxed(lean_object* v_as_4407_, lean_object* v_sz_4408_, lean_object* v_i_4409_, lean_object* v_b_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
size_t v_sz_boxed_4416_; size_t v_i_boxed_4417_; lean_object* v_res_4418_; 
v_sz_boxed_4416_ = lean_unbox_usize(v_sz_4408_);
lean_dec(v_sz_4408_);
v_i_boxed_4417_ = lean_unbox_usize(v_i_4409_);
lean_dec(v_i_4409_);
v_res_4418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_as_4407_, v_sz_boxed_4416_, v_i_boxed_4417_, v_b_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec_ref(v_as_4407_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f(lean_object* v_targets_4422_, uint8_t v_induction_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_){
_start:
{
lean_object* v___x_4429_; size_t v_sz_4430_; size_t v___x_4431_; lean_object* v___x_4432_; 
v___x_4429_ = ((lean_object*)(l_Lean_Meta_getCustomEliminator_x3f___closed__0));
v_sz_4430_ = lean_array_size(v_targets_4422_);
v___x_4431_ = ((size_t)0ULL);
v___x_4432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_targets_4422_, v_sz_4430_, v___x_4431_, v___x_4429_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4464_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4435_ = v___x_4432_;
v_isShared_4436_ = v_isSharedCheck_4464_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4432_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4464_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v_fst_4437_; 
v_fst_4437_ = lean_ctor_get(v_a_4433_, 0);
if (lean_obj_tag(v_fst_4437_) == 0)
{
lean_object* v_snd_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4458_; 
v_snd_4438_ = lean_ctor_get(v_a_4433_, 1);
v_isSharedCheck_4458_ = !lean_is_exclusive(v_a_4433_);
if (v_isSharedCheck_4458_ == 0)
{
lean_object* v_unused_4459_; 
v_unused_4459_ = lean_ctor_get(v_a_4433_, 0);
lean_dec(v_unused_4459_);
v___x_4440_ = v_a_4433_;
v_isShared_4441_ = v_isSharedCheck_4458_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_snd_4438_);
lean_dec(v_a_4433_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4458_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4442_; lean_object* v_env_4443_; lean_object* v___x_4444_; lean_object* v_ext_4445_; lean_object* v_toEnvExtension_4446_; lean_object* v_asyncMode_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; 
v___x_4442_ = lean_st_ref_get(v_a_4427_);
v_env_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc_ref(v_env_4443_);
lean_dec(v___x_4442_);
v___x_4444_ = l_Lean_Meta_customEliminatorExt;
v_ext_4445_ = lean_ctor_get(v___x_4444_, 1);
v_toEnvExtension_4446_ = lean_ctor_get(v_ext_4445_, 0);
v_asyncMode_4447_ = lean_ctor_get(v_toEnvExtension_4446_, 2);
v___x_4448_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
v___x_4449_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4448_, v___x_4444_, v_env_4443_, v_asyncMode_4447_);
v___x_4450_ = lean_box(v_induction_4423_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v___x_4450_);
v___x_4452_ = v___x_4440_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4450_);
lean_ctor_set(v_reuseFailAlloc_4457_, 1, v_snd_4438_);
v___x_4452_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
lean_object* v___x_4453_; lean_object* v___x_4455_; 
v___x_4453_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v___x_4449_, v___x_4452_);
lean_dec_ref(v___x_4452_);
lean_dec(v___x_4449_);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 0, v___x_4453_);
v___x_4455_ = v___x_4435_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4453_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
else
{
lean_object* v_val_4460_; lean_object* v___x_4462_; 
lean_inc_ref(v_fst_4437_);
lean_dec(v_a_4433_);
v_val_4460_ = lean_ctor_get(v_fst_4437_, 0);
lean_inc(v_val_4460_);
lean_dec_ref_known(v_fst_4437_, 1);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 0, v_val_4460_);
v___x_4462_ = v___x_4435_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_val_4460_);
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
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
v_a_4465_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4432_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4432_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f___boxed(lean_object* v_targets_4473_, lean_object* v_induction_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
uint8_t v_induction_boxed_4480_; lean_object* v_res_4481_; 
v_induction_boxed_4480_ = lean_unbox(v_induction_4474_);
v_res_4481_ = l_Lean_Meta_getCustomEliminator_x3f(v_targets_4473_, v_induction_boxed_4480_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_);
lean_dec(v_a_4478_);
lean_dec_ref(v_a_4477_);
lean_dec(v_a_4476_);
lean_dec_ref(v_a_4475_);
lean_dec_ref(v_targets_4473_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(lean_object* v_00_u03b2_4482_, lean_object* v_x_4483_, lean_object* v_x_4484_){
_start:
{
lean_object* v___x_4485_; 
v___x_4485_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v_x_4483_, v_x_4484_);
return v___x_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___boxed(lean_object* v_00_u03b2_4486_, lean_object* v_x_4487_, lean_object* v_x_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(v_00_u03b2_4486_, v_x_4487_, v_x_4488_);
lean_dec_ref(v_x_4488_);
lean_dec_ref(v_x_4487_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(lean_object* v_00_u03b2_4490_, lean_object* v_x_4491_, lean_object* v_x_4492_){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_4491_, v_x_4492_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4494_, lean_object* v_x_4495_, lean_object* v_x_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(v_00_u03b2_4494_, v_x_4495_, v_x_4496_);
lean_dec_ref(v_x_4496_);
lean_dec_ref(v_x_4495_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(lean_object* v_00_u03b2_4498_, lean_object* v_m_4499_, lean_object* v_a_4500_){
_start:
{
lean_object* v___x_4501_; 
v___x_4501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_4499_, v_a_4500_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4502_, lean_object* v_m_4503_, lean_object* v_a_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(v_00_u03b2_4502_, v_m_4503_, v_a_4504_);
lean_dec_ref(v_a_4504_);
lean_dec_ref(v_m_4503_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_4506_, lean_object* v_x_4507_, size_t v_x_4508_, lean_object* v_x_4509_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4507_, v_x_4508_, v_x_4509_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4511_, lean_object* v_x_4512_, lean_object* v_x_4513_, lean_object* v_x_4514_){
_start:
{
size_t v_x_2392__boxed_4515_; lean_object* v_res_4516_; 
v_x_2392__boxed_4515_ = lean_unbox_usize(v_x_4513_);
lean_dec(v_x_4513_);
v_res_4516_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(v_00_u03b2_4511_, v_x_4512_, v_x_2392__boxed_4515_, v_x_4514_);
lean_dec_ref(v_x_4514_);
lean_dec_ref(v_x_4512_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4517_, lean_object* v_m_4518_, lean_object* v_query_4519_){
_start:
{
lean_object* v___x_4520_; 
v___x_4520_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_m_4518_, v_query_4519_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4521_, lean_object* v_m_4522_, lean_object* v_query_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(v_00_u03b2_4521_, v_m_4522_, v_query_4523_);
lean_dec_ref(v_query_4523_);
lean_dec_ref(v_m_4522_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4525_, lean_object* v_keys_4526_, lean_object* v_vals_4527_, lean_object* v_heq_4528_, lean_object* v_i_4529_, lean_object* v_k_4530_){
_start:
{
lean_object* v___x_4531_; 
v___x_4531_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_4526_, v_vals_4527_, v_i_4529_, v_k_4530_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4532_, lean_object* v_keys_4533_, lean_object* v_vals_4534_, lean_object* v_heq_4535_, lean_object* v_i_4536_, lean_object* v_k_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(v_00_u03b2_4532_, v_keys_4533_, v_vals_4534_, v_heq_4535_, v_i_4536_, v_k_4537_);
lean_dec_ref(v_k_4537_);
lean_dec_ref(v_vals_4534_);
lean_dec_ref(v_keys_4533_);
return v_res_4538_;
}
}
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedElimInfo_default = _init_l_Lean_Meta_instInhabitedElimInfo_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedElimInfo_default);
l_Lean_Meta_instInhabitedElimInfo = _init_l_Lean_Meta_instInhabitedElimInfo();
lean_mark_persistent(l_Lean_Meta_instInhabitedElimInfo);
l_Lean_Meta_instInhabitedCustomEliminators_default = _init_l_Lean_Meta_instInhabitedCustomEliminators_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedCustomEliminators_default);
l_Lean_Meta_instInhabitedCustomEliminators = _init_l_Lean_Meta_instInhabitedCustomEliminators();
lean_mark_persistent(l_Lean_Meta_instInhabitedCustomEliminators);
res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_customEliminatorExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_customEliminatorExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_ElimInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_ElimInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_ElimInfo(builtin);
}
#ifdef __cplusplus
}
#endif
