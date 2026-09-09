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
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCustomEliminators;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprCustomEliminators___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprCustomEliminators_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprCustomEliminators___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprCustomEliminators = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators___closed__0_value;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminatorEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
lean_dec(v_x_129_);
return v_x_130_;
}
else
{
lean_object* v_head_132_; lean_object* v_tail_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_144_; 
v_head_132_ = lean_ctor_get(v_x_131_, 0);
v_tail_133_ = lean_ctor_get(v_x_131_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_144_ == 0)
{
v___x_135_ = v_x_131_;
v_isShared_136_ = v_isSharedCheck_144_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_tail_133_);
lean_inc(v_head_132_);
lean_dec(v_x_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_144_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
lean_inc(v_x_129_);
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 5);
lean_ctor_set(v___x_135_, 1, v_x_129_);
lean_ctor_set(v___x_135_, 0, v_x_130_);
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_x_130_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_x_129_);
v___x_138_ = v_reuseFailAlloc_143_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = l_Nat_reprFast(v_head_132_);
v___x_140_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
v___x_141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v_x_130_ = v___x_141_;
v_x_131_ = v_tail_133_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1(lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_dec(v_x_145_);
return v_x_146_;
}
else
{
lean_object* v_head_148_; lean_object* v_tail_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_160_; 
v_head_148_ = lean_ctor_get(v_x_147_, 0);
v_tail_149_ = lean_ctor_get(v_x_147_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_160_ == 0)
{
v___x_151_ = v_x_147_;
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_tail_149_);
lean_inc(v_head_148_);
lean_dec(v_x_147_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
lean_inc(v_x_145_);
if (v_isShared_152_ == 0)
{
lean_ctor_set_tag(v___x_151_, 5);
lean_ctor_set(v___x_151_, 1, v_x_145_);
lean_ctor_set(v___x_151_, 0, v_x_146_);
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_x_146_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_x_145_);
v___x_154_ = v_reuseFailAlloc_159_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_155_ = l_Nat_reprFast(v_head_148_);
v___x_156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_154_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(v_x_145_, v___x_157_, v_tail_149_);
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(lean_object* v___y_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = l_Nat_reprFast(v___y_161_);
v___x_163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
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
lean_object* v___x_491_; lean_object* v_env_492_; lean_object* v___x_493_; lean_object* v_toCold_494_; lean_object* v_mctx_495_; lean_object* v_lctx_496_; lean_object* v_options_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_491_ = lean_st_ref_get(v___y_489_);
v_env_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_env_492_);
lean_dec(v___x_491_);
v___x_493_ = lean_st_ref_get(v___y_487_);
v_toCold_494_ = lean_ctor_get(v___y_488_, 0);
v_mctx_495_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_mctx_495_);
lean_dec(v___x_493_);
v_lctx_496_ = lean_ctor_get(v___y_486_, 2);
v_options_497_ = lean_ctor_get(v_toCold_494_, 2);
lean_inc_ref(v_options_497_);
lean_inc_ref(v_lctx_496_);
v___x_498_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_498_, 0, v_env_492_);
lean_ctor_set(v___x_498_, 1, v_mctx_495_);
lean_ctor_set(v___x_498_, 2, v_lctx_496_);
lean_ctor_set(v___x_498_, 3, v_options_497_);
v___x_499_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_msgData_485_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2___boxed(lean_object* v_msgData_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msgData_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(lean_object* v_msg_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_ref_514_; lean_object* v___x_515_; lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_524_; 
v_ref_514_ = lean_ctor_get(v___y_511_, 2);
v___x_515_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_524_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_inc(v_ref_514_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_ref_514_);
lean_ctor_set(v___x_520_, 1, v_a_516_);
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 1);
lean_ctor_set(v___x_518_, 0, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg___boxed(lean_object* v_msg_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_531_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(lean_object* v_a_544_, lean_object* v_x_545_, lean_object* v_motiveParams_546_, lean_object* v_motiveResultType_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_561_ = lean_array_get_size(v_motiveParams_546_);
v___x_562_ = lean_array_get_size(v_x_545_);
v___x_563_ = lean_nat_dec_eq(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_564_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3);
v___x_565_ = l_Nat_reprFast(v___x_562_);
v___x_566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
v___x_567_ = l_Lean_MessageData_ofFormat(v___x_566_);
v___x_568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_564_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l_Nat_reprFast(v___x_561_);
v___x_572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
v___x_573_ = l_Lean_MessageData_ofFormat(v___x_572_);
v___x_574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_570_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7);
v___x_576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = l_Lean_indentExpr(v_a_544_);
v___x_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_578_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
return v___x_579_;
}
else
{
goto v___jp_553_;
}
v___jp_553_:
{
uint8_t v___x_554_; 
v___x_554_ = l_Lean_Expr_isSort(v_motiveResultType_547_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_555_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1);
v___x_556_ = l_Lean_indentExpr(v_a_544_);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_557_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref(v_a_544_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed(lean_object* v_a_580_, lean_object* v_x_581_, lean_object* v_motiveParams_582_, lean_object* v_motiveResultType_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(v_a_580_, v_x_581_, v_motiveParams_582_, v_motiveResultType_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v_motiveResultType_583_);
lean_dec_ref(v_motiveParams_582_);
lean_dec_ref(v_x_581_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(lean_object* v_xs_590_, lean_object* v_v_591_, lean_object* v_i_592_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_array_get_size(v_xs_590_);
v___x_594_ = lean_nat_dec_lt(v_i_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
lean_dec(v_i_592_);
v___x_595_ = lean_box(0);
return v___x_595_;
}
else
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_array_fget_borrowed(v_xs_590_, v_i_592_);
v___x_597_ = lean_expr_eqv(v___x_596_, v_v_591_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_i_592_, v___x_598_);
lean_dec(v_i_592_);
v_i_592_ = v___x_599_;
goto _start;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_i_592_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2___boxed(lean_object* v_xs_602_, lean_object* v_v_603_, lean_object* v_i_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(v_xs_602_, v_v_603_, v_i_604_);
lean_dec_ref(v_v_603_);
lean_dec_ref(v_xs_602_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(lean_object* v_xs_606_, lean_object* v_v_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(v_xs_606_, v_v_607_, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0___boxed(lean_object* v_xs_610_, lean_object* v_v_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(v_xs_610_, v_v_611_);
lean_dec_ref(v_v_611_);
lean_dec_ref(v_xs_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(lean_object* v_xs_613_, lean_object* v_v_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(v_xs_613_, v_v_614_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v___x_616_; 
v___x_616_ = lean_box(0);
return v___x_616_;
}
else
{
lean_object* v_val_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_val_617_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_615_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_val_617_);
lean_dec(v___x_615_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_val_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0___boxed(lean_object* v_xs_625_, lean_object* v_v_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_625_, v_v_626_);
lean_dec_ref(v_v_626_);
lean_dec_ref(v_xs_625_);
return v_res_627_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(lean_object* v_xs_631_, lean_object* v_a_632_, size_t v_sz_633_, size_t v_i_634_, lean_object* v_bs_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = lean_usize_dec_lt(v_i_634_, v_sz_633_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_dec_ref(v_a_632_);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v_bs_635_);
return v___x_642_;
}
else
{
lean_object* v_v_643_; lean_object* v___x_644_; lean_object* v_bs_x27_645_; lean_object* v_a_647_; lean_object* v___x_652_; 
v_v_643_ = lean_array_uget(v_bs_635_, v_i_634_);
v___x_644_ = lean_unsigned_to_nat(0u);
v_bs_x27_645_ = lean_array_uset(v_bs_635_, v_i_634_, v___x_644_);
v___x_652_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_631_, v_v_643_);
lean_dec(v_v_643_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
lean_inc_ref(v_a_632_);
v___x_654_ = l_Lean_indentExpr(v_a_632_);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_655_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v_a_647_ = v_a_657_;
goto v___jp_646_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_bs_x27_645_);
lean_dec_ref(v_a_632_);
v_a_658_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_656_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_val_666_; 
v_val_666_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v___x_652_, 1);
v_a_647_ = v_val_666_;
goto v___jp_646_;
}
v___jp_646_:
{
size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_634_, v___x_648_);
v___x_650_ = lean_array_uset(v_bs_x27_645_, v_i_634_, v_a_647_);
v_i_634_ = v___x_649_;
v_bs_635_ = v___x_650_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___boxed(lean_object* v_xs_667_, lean_object* v_a_668_, lean_object* v_sz_669_, lean_object* v_i_670_, lean_object* v_bs_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
size_t v_sz_boxed_677_; size_t v_i_boxed_678_; lean_object* v_res_679_; 
v_sz_boxed_677_ = lean_unbox_usize(v_sz_669_);
lean_dec(v_sz_669_);
v_i_boxed_678_ = lean_unbox_usize(v_i_670_);
lean_dec(v_i_670_);
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_667_, v_a_668_, v_sz_boxed_677_, v_i_boxed_678_, v_bs_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec_ref(v_xs_667_);
return v_res_679_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(lean_object* v_a_680_, lean_object* v_as_681_, size_t v_i_682_, size_t v_stop_683_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = lean_usize_dec_eq(v_i_682_, v_stop_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_array_uget_borrowed(v_as_681_, v_i_682_);
v___x_686_ = lean_expr_eqv(v_a_680_, v___x_685_);
if (v___x_686_ == 0)
{
size_t v___x_687_; size_t v___x_688_; 
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_add(v_i_682_, v___x_687_);
v_i_682_ = v___x_688_;
goto _start;
}
else
{
return v___x_686_;
}
}
else
{
uint8_t v___x_690_; 
v___x_690_ = 0;
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6___boxed(lean_object* v_a_691_, lean_object* v_as_692_, lean_object* v_i_693_, lean_object* v_stop_694_){
_start:
{
size_t v_i_boxed_695_; size_t v_stop_boxed_696_; uint8_t v_res_697_; lean_object* v_r_698_; 
v_i_boxed_695_ = lean_unbox_usize(v_i_693_);
lean_dec(v_i_693_);
v_stop_boxed_696_ = lean_unbox_usize(v_stop_694_);
lean_dec(v_stop_694_);
v_res_697_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(v_a_691_, v_as_692_, v_i_boxed_695_, v_stop_boxed_696_);
lean_dec_ref(v_as_692_);
lean_dec_ref(v_a_691_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(lean_object* v_as_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_array_get_size(v_as_699_);
v___x_703_ = lean_nat_dec_lt(v___x_701_, v___x_702_);
if (v___x_703_ == 0)
{
return v___x_703_;
}
else
{
if (v___x_703_ == 0)
{
return v___x_703_;
}
else
{
size_t v___x_704_; size_t v___x_705_; uint8_t v___x_706_; 
v___x_704_ = ((size_t)0ULL);
v___x_705_ = lean_usize_of_nat(v___x_702_);
v___x_706_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(v_a_700_, v_as_699_, v___x_704_, v___x_705_);
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4___boxed(lean_object* v_as_707_, lean_object* v_a_708_){
_start:
{
uint8_t v_res_709_; lean_object* v_r_710_; 
v_res_709_ = l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(v_as_707_, v_a_708_);
lean_dec_ref(v_a_708_);
lean_dec_ref(v_as_707_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(lean_object* v_upperBound_711_, lean_object* v_xs_712_, lean_object* v_motive_713_, lean_object* v___x_714_, lean_object* v_baseDeclName_x3f_715_, lean_object* v___x_716_, lean_object* v_a_717_, lean_object* v_b_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_a_724_; uint8_t v___x_728_; 
v___x_728_ = lean_nat_dec_lt(v_a_717_, v_upperBound_711_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v_a_717_);
lean_dec_ref(v___x_716_);
lean_dec(v_baseDeclName_x3f_715_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_b_718_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_array_fget_borrowed(v_xs_712_, v_a_717_);
v___x_731_ = lean_expr_eqv(v___x_730_, v_motive_713_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; 
v___x_732_ = l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(v___x_714_, v___x_730_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = l_Lean_Expr_fvarId_x21(v___x_730_);
v___x_734_ = l_Lean_FVarId_getDecl___redArg(v___x_733_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; uint8_t v___x_736_; uint8_t v___x_737_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = l_Lean_LocalDecl_binderInfo(v_a_735_);
v___x_737_ = l_Lean_BinderInfo_isExplicit(v___x_736_);
if (v___x_737_ == 0)
{
lean_dec(v_a_735_);
v_a_724_ = v_b_718_;
goto v___jp_723_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_fst_741_; lean_object* v_snd_742_; lean_object* v___x_743_; lean_object* v___y_745_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = l_Lean_LocalDecl_type(v_a_735_);
v___x_740_ = l_Lean_Meta_altArity(v_motive_713_, v___x_738_, v___x_739_);
lean_dec_ref(v___x_739_);
v_fst_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_fst_741_);
v_snd_742_ = lean_ctor_get(v___x_740_, 1);
lean_inc(v_snd_742_);
lean_dec_ref(v___x_740_);
v___x_743_ = l_Lean_LocalDecl_userName(v_a_735_);
lean_dec(v_a_735_);
if (lean_obj_tag(v_baseDeclName_x3f_715_) == 0)
{
v___y_745_ = v_baseDeclName_x3f_715_;
goto v___jp_744_;
}
else
{
lean_object* v_val_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_val_749_ = lean_ctor_get(v_baseDeclName_x3f_715_, 0);
lean_inc(v___x_743_);
lean_inc(v_val_749_);
v___x_750_ = l_Lean_Name_append(v_val_749_, v___x_743_);
lean_inc(v___x_750_);
lean_inc_ref(v___x_716_);
v___x_751_ = l_Lean_Environment_contains(v___x_716_, v___x_750_, v___x_728_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_dec(v___x_750_);
v___x_752_ = lean_box(0);
v___y_745_ = v___x_752_;
goto v___jp_744_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_750_);
v___y_745_ = v___x_753_;
goto v___jp_744_;
}
}
v___jp_744_:
{
lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_746_, 0, v___x_743_);
lean_ctor_set(v___x_746_, 1, v___y_745_);
lean_ctor_set(v___x_746_, 2, v_fst_741_);
v___x_747_ = lean_unbox(v_snd_742_);
lean_dec(v_snd_742_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*3, v___x_747_);
v___x_748_ = lean_array_push(v_b_718_, v___x_746_);
v_a_724_ = v___x_748_;
goto v___jp_723_;
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v_b_718_);
lean_dec(v_a_717_);
lean_dec_ref(v___x_716_);
lean_dec(v_baseDeclName_x3f_715_);
v_a_754_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_734_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_734_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
v_a_724_ = v_b_718_;
goto v___jp_723_;
}
}
else
{
v_a_724_ = v_b_718_;
goto v___jp_723_;
}
}
v___jp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_a_717_, v___x_725_);
lean_dec(v_a_717_);
v_a_717_ = v___x_726_;
v_b_718_ = v_a_724_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg___boxed(lean_object* v_upperBound_762_, lean_object* v_xs_763_, lean_object* v_motive_764_, lean_object* v___x_765_, lean_object* v_baseDeclName_x3f_766_, lean_object* v___x_767_, lean_object* v_a_768_, lean_object* v_b_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v_upperBound_762_, v_xs_763_, v_motive_764_, v___x_765_, v_baseDeclName_x3f_766_, v___x_767_, v_a_768_, v_b_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec_ref(v___x_765_);
lean_dec_ref(v_motive_764_);
lean_dec_ref(v_xs_763_);
lean_dec(v_upperBound_762_);
return v_res_774_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2));
v___x_780_ = l_Lean_stringToMessageData(v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(lean_object* v_xs_781_, lean_object* v_a_782_, lean_object* v_elimExpr_783_, lean_object* v_baseDeclName_x3f_784_, lean_object* v_type_785_, lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; 
if (lean_obj_tag(v_x_786_) == 5)
{
lean_object* v_fn_869_; lean_object* v_arg_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_fn_869_ = lean_ctor_get(v_x_786_, 0);
lean_inc_ref(v_fn_869_);
v_arg_870_ = lean_ctor_get(v_x_786_, 1);
lean_inc_ref(v_arg_870_);
lean_dec_ref_known(v_x_786_, 2);
v___x_871_ = lean_array_set(v_x_787_, v_x_788_, v_arg_870_);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_nat_sub(v_x_788_, v___x_872_);
lean_dec(v_x_788_);
v_x_786_ = v_fn_869_;
v_x_787_ = v___x_871_;
v_x_788_ = v___x_873_;
goto _start;
}
else
{
lean_object* v___f_875_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; uint8_t v___x_888_; 
lean_dec(v_x_788_);
v___f_875_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1));
v___x_888_ = l_Lean_Expr_isFVar(v_x_786_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v_x_787_);
lean_dec_ref(v_x_786_);
lean_dec(v_baseDeclName_x3f_784_);
lean_dec_ref(v_elimExpr_783_);
lean_dec_ref(v_a_782_);
v___x_889_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3);
v___x_890_ = l_Lean_indentExpr(v_type_785_);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_891_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
else
{
lean_dec_ref(v_type_785_);
v___y_877_ = v___y_789_;
v___y_878_ = v___y_790_;
v___y_879_ = v___y_791_;
v___y_880_ = v___y_792_;
goto v___jp_876_;
}
v___jp_876_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_881_ = l_Array_takeWhile___redArg(v___f_875_, v_x_787_);
v___x_882_ = lean_array_get_size(v___x_881_);
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_array_get_size(v_x_787_);
v___x_885_ = lean_nat_dec_le(v___x_882_, v___x_883_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_882_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
v___y_795_ = v___y_877_;
v___y_796_ = v___y_880_;
v___y_797_ = v___x_881_;
v___y_798_ = v___y_879_;
v___y_799_ = v___y_878_;
v___y_800_ = v___x_886_;
goto v___jp_794_;
}
else
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_883_);
lean_ctor_set(v___x_887_, 1, v___x_884_);
v___y_795_ = v___y_877_;
v___y_796_ = v___y_880_;
v___y_797_ = v___x_881_;
v___y_798_ = v___y_879_;
v___y_799_ = v___y_878_;
v___y_800_ = v___x_887_;
goto v___jp_794_;
}
}
}
v___jp_794_:
{
lean_object* v___x_801_; 
lean_inc(v___y_796_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_795_);
lean_inc_ref(v_x_786_);
v___x_801_ = lean_infer_type(v_x_786_, v___y_795_, v___y_799_, v___y_798_, v___y_796_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___f_803_; uint8_t v___x_804_; lean_object* v___x_805_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc_n(v_a_802_, 2);
lean_dec_ref_known(v___x_801_, 1);
lean_inc_ref(v_x_787_);
v___f_803_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed), 9, 2);
lean_closure_set(v___f_803_, 0, v_a_802_);
lean_closure_set(v___f_803_, 1, v_x_787_);
v___x_804_ = 0;
v___x_805_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_802_, v___f_803_, v___x_804_, v___x_804_, v___y_795_, v___y_799_, v___y_798_, v___y_796_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_806_; 
lean_dec_ref_known(v___x_805_, 1);
v___x_806_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_781_, v_x_786_);
if (lean_obj_tag(v___x_806_) == 1)
{
lean_object* v_val_807_; size_t v_sz_808_; size_t v___x_809_; lean_object* v___x_810_; 
v_val_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_val_807_);
lean_dec_ref_known(v___x_806_, 1);
v_sz_808_ = lean_array_size(v___y_797_);
v___x_809_ = ((size_t)0ULL);
lean_inc_ref(v___y_797_);
lean_inc_ref(v_a_782_);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_781_, v_a_782_, v_sz_808_, v___x_809_, v___y_797_, v___y_795_, v___y_799_, v___y_798_, v___y_796_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; lean_object* v_lower_813_; lean_object* v_upper_814_; lean_object* v_env_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v___x_812_ = lean_st_ref_get(v___y_796_);
v_lower_813_ = lean_ctor_get(v___y_800_, 0);
lean_inc(v_lower_813_);
v_upper_814_ = lean_ctor_get(v___y_800_, 1);
lean_inc(v_upper_814_);
lean_dec_ref(v___y_800_);
v_env_815_ = lean_ctor_get(v___x_812_, 0);
lean_inc_ref(v_env_815_);
lean_dec(v___x_812_);
v___x_816_ = lean_array_get_size(v_xs_781_);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0));
v___x_819_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v___x_816_, v_xs_781_, v_x_786_, v___y_797_, v_baseDeclName_x3f_784_, v_env_815_, v___x_817_, v___x_818_, v___y_795_, v___y_798_, v___y_796_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_x_786_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_832_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_832_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_832_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_832_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v_start_825_; lean_object* v_stop_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_824_ = l_Array_toSubarray___redArg(v_x_787_, v_lower_813_, v_upper_814_);
v_start_825_ = lean_ctor_get(v___x_824_, 1);
lean_inc(v_start_825_);
v_stop_826_ = lean_ctor_get(v___x_824_, 2);
lean_inc(v_stop_826_);
lean_dec_ref(v___x_824_);
v___x_827_ = lean_nat_sub(v_stop_826_, v_start_825_);
lean_dec(v_start_825_);
lean_dec(v_stop_826_);
v___x_828_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_828_, 0, v_elimExpr_783_);
lean_ctor_set(v___x_828_, 1, v_a_782_);
lean_ctor_set(v___x_828_, 2, v_val_807_);
lean_ctor_set(v___x_828_, 3, v_a_811_);
lean_ctor_set(v___x_828_, 4, v_a_820_);
lean_ctor_set(v___x_828_, 5, v___x_827_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_828_);
v___x_830_ = v___x_822_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_upper_814_);
lean_dec(v_lower_813_);
lean_dec(v_a_811_);
lean_dec(v_val_807_);
lean_dec_ref(v_x_787_);
lean_dec_ref(v_elimExpr_783_);
lean_dec_ref(v_a_782_);
v_a_833_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_819_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_819_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v_val_807_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_x_787_);
lean_dec_ref(v_x_786_);
lean_dec(v_baseDeclName_x3f_784_);
lean_dec_ref(v_elimExpr_783_);
lean_dec_ref(v_a_782_);
v_a_841_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_810_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_810_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v___x_806_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_x_787_);
lean_dec_ref(v_x_786_);
lean_dec(v_baseDeclName_x3f_784_);
lean_dec_ref(v_elimExpr_783_);
v___x_849_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
v___x_850_ = l_Lean_indentExpr(v_a_782_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_851_, v___y_795_, v___y_799_, v___y_798_, v___y_796_);
return v___x_852_;
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec_ref(v___y_800_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_x_787_);
lean_dec_ref(v_x_786_);
lean_dec(v_baseDeclName_x3f_784_);
lean_dec_ref(v_elimExpr_783_);
lean_dec_ref(v_a_782_);
v_a_853_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_805_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_805_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
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
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec_ref(v___y_800_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_x_787_);
lean_dec_ref(v_x_786_);
lean_dec(v_baseDeclName_x3f_784_);
lean_dec_ref(v_elimExpr_783_);
lean_dec_ref(v_a_782_);
v_a_861_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_801_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_801_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___boxed(lean_object* v_xs_901_, lean_object* v_a_902_, lean_object* v_elimExpr_903_, lean_object* v_baseDeclName_x3f_904_, lean_object* v_type_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(v_xs_901_, v_a_902_, v_elimExpr_903_, v_baseDeclName_x3f_904_, v_type_905_, v_x_906_, v_x_907_, v_x_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec_ref(v_xs_901_);
return v_res_914_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0(void){
_start:
{
lean_object* v___x_915_; lean_object* v_dummy_916_; 
v___x_915_ = lean_box(0);
v_dummy_916_ = l_Lean_Expr_sort___override(v___x_915_);
return v_dummy_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0(lean_object* v_a_917_, lean_object* v_elimExpr_918_, lean_object* v_baseDeclName_x3f_919_, lean_object* v_xs_920_, lean_object* v_type_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_dummy_927_; lean_object* v_nargs_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_dummy_927_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___lam__0___closed__0, &l_Lean_Meta_getElimExprInfo___lam__0___closed__0_once, _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0);
v_nargs_928_ = l_Lean_Expr_getAppNumArgs(v_type_921_);
lean_inc(v_nargs_928_);
v___x_929_ = lean_mk_array(v_nargs_928_, v_dummy_927_);
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_nat_sub(v_nargs_928_, v___x_930_);
lean_dec(v_nargs_928_);
lean_inc_ref(v_type_921_);
v___x_932_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(v_xs_920_, v_a_917_, v_elimExpr_918_, v_baseDeclName_x3f_919_, v_type_921_, v_type_921_, v___x_929_, v___x_931_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0___boxed(lean_object* v_a_933_, lean_object* v_elimExpr_934_, lean_object* v_baseDeclName_x3f_935_, lean_object* v_xs_936_, lean_object* v_type_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Meta_getElimExprInfo___lam__0(v_a_933_, v_elimExpr_934_, v_baseDeclName_x3f_935_, v_xs_936_, v_type_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec_ref(v_xs_936_);
return v_res_943_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0(void){
_start:
{
lean_object* v___x_944_; double v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_float_of_nat(v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(lean_object* v_cls_949_, lean_object* v_msg_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_ref_956_; lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_1002_; 
v_ref_956_ = lean_ctor_get(v___y_953_, 2);
v___x_957_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_1002_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_1002_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v_traceState_963_; lean_object* v_env_964_; lean_object* v_nextMacroScope_965_; lean_object* v_ngen_966_; lean_object* v_auxDeclNGen_967_; lean_object* v_cache_968_; lean_object* v_messages_969_; lean_object* v_infoState_970_; lean_object* v_snapshotTasks_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1001_; 
v___x_962_ = lean_st_ref_take(v___y_954_);
v_traceState_963_ = lean_ctor_get(v___x_962_, 4);
v_env_964_ = lean_ctor_get(v___x_962_, 0);
v_nextMacroScope_965_ = lean_ctor_get(v___x_962_, 1);
v_ngen_966_ = lean_ctor_get(v___x_962_, 2);
v_auxDeclNGen_967_ = lean_ctor_get(v___x_962_, 3);
v_cache_968_ = lean_ctor_get(v___x_962_, 5);
v_messages_969_ = lean_ctor_get(v___x_962_, 6);
v_infoState_970_ = lean_ctor_get(v___x_962_, 7);
v_snapshotTasks_971_ = lean_ctor_get(v___x_962_, 8);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_973_ = v___x_962_;
v_isShared_974_ = v_isSharedCheck_1001_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_snapshotTasks_971_);
lean_inc(v_infoState_970_);
lean_inc(v_messages_969_);
lean_inc(v_cache_968_);
lean_inc(v_traceState_963_);
lean_inc(v_auxDeclNGen_967_);
lean_inc(v_ngen_966_);
lean_inc(v_nextMacroScope_965_);
lean_inc(v_env_964_);
lean_dec(v___x_962_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1001_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
uint64_t v_tid_975_; lean_object* v_traces_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1000_; 
v_tid_975_ = lean_ctor_get_uint64(v_traceState_963_, sizeof(void*)*1);
v_traces_976_ = lean_ctor_get(v_traceState_963_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_traceState_963_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_978_ = v_traceState_963_;
v_isShared_979_ = v_isSharedCheck_1000_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_traces_976_);
lean_dec(v_traceState_963_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1000_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; double v___x_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_980_ = lean_box(0);
v___x_981_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0, &l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0);
v___x_982_ = 0;
v___x_983_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1));
v___x_984_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_984_, 0, v_cls_949_);
lean_ctor_set(v___x_984_, 1, v___x_980_);
lean_ctor_set(v___x_984_, 2, v___x_983_);
lean_ctor_set_float(v___x_984_, sizeof(void*)*3, v___x_981_);
lean_ctor_set_float(v___x_984_, sizeof(void*)*3 + 8, v___x_981_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*3 + 16, v___x_982_);
v___x_985_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2));
v___x_986_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v_a_958_);
lean_ctor_set(v___x_986_, 2, v___x_985_);
lean_inc(v_ref_956_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_ref_956_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Lean_PersistentArray_push___redArg(v_traces_976_, v___x_987_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_988_);
v___x_990_ = v___x_978_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_988_);
lean_ctor_set_uint64(v_reuseFailAlloc_999_, sizeof(void*)*1, v_tid_975_);
v___x_990_ = v_reuseFailAlloc_999_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_992_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 4, v___x_990_);
v___x_992_ = v___x_973_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_env_964_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_nextMacroScope_965_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_ngen_966_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_auxDeclNGen_967_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_998_, 5, v_cache_968_);
lean_ctor_set(v_reuseFailAlloc_998_, 6, v_messages_969_);
lean_ctor_set(v_reuseFailAlloc_998_, 7, v_infoState_970_);
lean_ctor_set(v_reuseFailAlloc_998_, 8, v_snapshotTasks_971_);
v___x_992_ = v_reuseFailAlloc_998_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_993_ = lean_st_ref_put(v___y_954_, v___x_992_);
v___x_994_ = lean_box(0);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_994_);
v___x_996_ = v___x_960_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___boxed(lean_object* v_cls_1003_, lean_object* v_msg_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(v_cls_1003_, v_msg_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1010_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__5(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__2));
v___x_1020_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__4));
v___x_1021_ = l_Lean_Name_append(v___x_1020_, v___x_1019_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__7(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__6));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__9(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__8));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo(lean_object* v_elimExpr_1028_, lean_object* v_baseDeclName_x3f_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; 
lean_inc(v_a_1033_);
lean_inc_ref(v_a_1032_);
lean_inc(v_a_1031_);
lean_inc_ref(v_a_1030_);
lean_inc_ref(v_elimExpr_1028_);
v___x_1035_ = lean_infer_type(v_elimExpr_1028_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_toCold_1036_; lean_object* v_options_1037_; lean_object* v_a_1038_; lean_object* v_inheritedTraceOptions_1039_; uint8_t v_hasTrace_1040_; lean_object* v___f_1041_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; 
v_toCold_1036_ = lean_ctor_get(v_a_1032_, 0);
v_options_1037_ = lean_ctor_get(v_toCold_1036_, 2);
v_a_1038_ = lean_ctor_get(v___x_1035_, 0);
lean_inc_n(v_a_1038_, 2);
lean_dec_ref_known(v___x_1035_, 1);
v_inheritedTraceOptions_1039_ = lean_ctor_get(v_toCold_1036_, 11);
v_hasTrace_1040_ = lean_ctor_get_uint8(v_options_1037_, sizeof(void*)*1);
lean_inc_ref(v_elimExpr_1028_);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_Meta_getElimExprInfo___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1041_, 0, v_a_1038_);
lean_closure_set(v___f_1041_, 1, v_elimExpr_1028_);
lean_closure_set(v___f_1041_, 2, v_baseDeclName_x3f_1029_);
if (v_hasTrace_1040_ == 0)
{
lean_dec_ref(v_elimExpr_1028_);
v___y_1043_ = v_a_1030_;
v___y_1044_ = v_a_1031_;
v___y_1045_ = v_a_1032_;
v___y_1046_ = v_a_1033_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1049_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__2));
v___x_1050_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__5, &l_Lean_Meta_getElimExprInfo___closed__5_once, _init_l_Lean_Meta_getElimExprInfo___closed__5);
v___x_1051_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1039_, v_options_1037_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_dec_ref(v_elimExpr_1028_);
v___y_1043_ = v_a_1030_;
v___y_1044_ = v_a_1031_;
v___y_1045_ = v_a_1032_;
v___y_1046_ = v_a_1033_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1052_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__7, &l_Lean_Meta_getElimExprInfo___closed__7_once, _init_l_Lean_Meta_getElimExprInfo___closed__7);
v___x_1053_ = l_Lean_indentExpr(v_elimExpr_1028_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__9, &l_Lean_Meta_getElimExprInfo___closed__9_once, _init_l_Lean_Meta_getElimExprInfo___closed__9);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
lean_inc(v_a_1038_);
v___x_1057_ = l_Lean_indentExpr(v_a_1038_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(v___x_1049_, v___x_1058_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_dec_ref_known(v___x_1059_, 1);
v___y_1043_ = v_a_1030_;
v___y_1044_ = v_a_1031_;
v___y_1045_ = v_a_1032_;
v___y_1046_ = v_a_1033_;
goto v___jp_1042_;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec_ref(v___f_1041_);
lean_dec(v_a_1038_);
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
v___jp_1042_:
{
uint8_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = 0;
v___x_1048_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_1038_, v___f_1041_, v___x_1047_, v___x_1047_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1048_;
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_baseDeclName_x3f_1029_);
lean_dec_ref(v_elimExpr_1028_);
v_a_1068_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1035_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1035_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___boxed(lean_object* v_elimExpr_1076_, lean_object* v_baseDeclName_x3f_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Meta_getElimExprInfo(v_elimExpr_1076_, v_baseDeclName_x3f_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(lean_object* v_00_u03b1_1084_, lean_object* v_msg_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(v_00_u03b1_1092_, v_msg_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(lean_object* v_upperBound_1100_, lean_object* v_xs_1101_, lean_object* v_motive_1102_, lean_object* v___x_1103_, lean_object* v_baseDeclName_x3f_1104_, lean_object* v___x_1105_, lean_object* v_inst_1106_, lean_object* v_R_1107_, lean_object* v_a_1108_, lean_object* v_b_1109_, lean_object* v_c_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v_upperBound_1100_, v_xs_1101_, v_motive_1102_, v___x_1103_, v_baseDeclName_x3f_1104_, v___x_1105_, v_a_1108_, v_b_1109_, v___y_1111_, v___y_1113_, v___y_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___boxed(lean_object* v_upperBound_1117_, lean_object* v_xs_1118_, lean_object* v_motive_1119_, lean_object* v___x_1120_, lean_object* v_baseDeclName_x3f_1121_, lean_object* v___x_1122_, lean_object* v_inst_1123_, lean_object* v_R_1124_, lean_object* v_a_1125_, lean_object* v_b_1126_, lean_object* v_c_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(v_upperBound_1117_, v_xs_1118_, v_motive_1119_, v___x_1120_, v_baseDeclName_x3f_1121_, v___x_1122_, v_inst_1123_, v_R_1124_, v_a_1125_, v_b_1126_, v_c_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v___x_1120_);
lean_dec_ref(v_motive_1119_);
lean_dec_ref(v_xs_1118_);
lean_dec(v_upperBound_1117_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object* v_elimName_1134_, lean_object* v_baseDeclName_x3f_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_elimName_1134_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = l_Lean_Meta_getElimExprInfo(v_a_1142_, v_baseDeclName_x3f_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v___x_1143_;
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_baseDeclName_x3f_1135_);
v_a_1144_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1141_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1141_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___boxed(lean_object* v_elimName_1152_, lean_object* v_baseDeclName_x3f_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Meta_getElimInfo(v_elimName_1152_, v_baseDeclName_x3f_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
return v_res_1159_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(lean_object* v_a_1160_, lean_object* v_as_1161_, size_t v_i_1162_, size_t v_stop_1163_){
_start:
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_usize_dec_eq(v_i_1162_, v_stop_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_array_uget_borrowed(v_as_1161_, v_i_1162_);
v___x_1166_ = lean_nat_dec_eq(v_a_1160_, v___x_1165_);
if (v___x_1166_ == 0)
{
size_t v___x_1167_; size_t v___x_1168_; 
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_add(v_i_1162_, v___x_1167_);
v_i_1162_ = v___x_1168_;
goto _start;
}
else
{
return v___x_1166_;
}
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = 0;
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0___boxed(lean_object* v_a_1171_, lean_object* v_as_1172_, lean_object* v_i_1173_, lean_object* v_stop_1174_){
_start:
{
size_t v_i_boxed_1175_; size_t v_stop_boxed_1176_; uint8_t v_res_1177_; lean_object* v_r_1178_; 
v_i_boxed_1175_ = lean_unbox_usize(v_i_1173_);
lean_dec(v_i_1173_);
v_stop_boxed_1176_ = lean_unbox_usize(v_stop_1174_);
lean_dec(v_stop_1174_);
v_res_1177_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_1171_, v_as_1172_, v_i_boxed_1175_, v_stop_boxed_1176_);
lean_dec_ref(v_as_1172_);
lean_dec(v_a_1171_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(lean_object* v_as_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = lean_array_get_size(v_as_1179_);
v___x_1183_ = lean_nat_dec_lt(v___x_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
return v___x_1183_;
}
else
{
if (v___x_1183_ == 0)
{
return v___x_1183_;
}
else
{
size_t v___x_1184_; size_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1184_ = ((size_t)0ULL);
v___x_1185_ = lean_usize_of_nat(v___x_1182_);
v___x_1186_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_1180_, v_as_1179_, v___x_1184_, v___x_1185_);
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0___boxed(lean_object* v_as_1187_, lean_object* v_a_1188_){
_start:
{
uint8_t v_res_1189_; lean_object* v_r_1190_; 
v_res_1189_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_as_1187_, v_a_1188_);
lean_dec(v_a_1188_);
lean_dec_ref(v_as_1187_);
v_r_1190_ = lean_box(v_res_1189_);
return v_r_1190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1));
v___x_1195_ = l_Lean_stringToMessageData(v___x_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3));
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5));
v___x_1201_ = l_Lean_stringToMessageData(v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7));
v___x_1204_ = l_Lean_stringToMessageData(v___x_1203_);
return v___x_1204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9));
v___x_1207_ = l_Lean_stringToMessageData(v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(lean_object* v_elimInfo_1208_, lean_object* v_targets_1209_, lean_object* v_type_1210_, lean_object* v_argIdx_1211_, lean_object* v_targetIdx_1212_, lean_object* v_implicits_1213_, lean_object* v_targets_x27_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Meta_whnfD(v_type_1210_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 1);
if (lean_obj_tag(v_a_1224_) == 7)
{
lean_object* v_binderName_1225_; lean_object* v_binderType_1226_; lean_object* v_body_1227_; uint8_t v_binderInfo_1228_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v_elimExpr_1241_; lean_object* v_targetsPos_1242_; uint8_t v___x_1243_; 
v_binderName_1225_ = lean_ctor_get(v_a_1224_, 0);
lean_inc(v_binderName_1225_);
v_binderType_1226_ = lean_ctor_get(v_a_1224_, 1);
lean_inc_ref(v_binderType_1226_);
v_body_1227_ = lean_ctor_get(v_a_1224_, 2);
lean_inc_ref(v_body_1227_);
v_binderInfo_1228_ = lean_ctor_get_uint8(v_a_1224_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1224_, 3);
v_elimExpr_1241_ = lean_ctor_get(v_elimInfo_1208_, 0);
v_targetsPos_1242_ = lean_ctor_get(v_elimInfo_1208_, 3);
v___x_1243_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_targetsPos_1242_, v_argIdx_1211_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec(v_binderName_1225_);
v___x_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1244_, 0, v_binderType_1226_);
v___x_1245_ = 0;
v___x_1246_ = lean_box(0);
v___x_1247_ = l_Lean_Meta_mkFreshExprMVar(v___x_1244_, v___x_1245_, v___x_1246_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1249_ = lean_expr_instantiate1(v_body_1227_, v_a_1248_);
lean_dec(v_a_1248_);
lean_dec_ref(v_body_1227_);
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v_argIdx_1211_, v___x_1250_);
lean_dec(v_argIdx_1211_);
v_type_1210_ = v___x_1249_;
v_argIdx_1211_ = v___x_1251_;
goto _start;
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1253_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1247_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1247_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1228_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_binderType_1226_);
v___x_1263_ = 0;
v___x_1264_ = l_Lean_Meta_mkFreshExprMVar(v___x_1262_, v___x_1263_, v_binderName_1225_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1266_ = lean_expr_instantiate1(v_body_1227_, v_a_1265_);
lean_dec_ref(v_body_1227_);
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_nat_add(v_argIdx_1211_, v___x_1267_);
lean_dec(v_argIdx_1211_);
v___x_1269_ = l_Lean_Expr_mvarId_x21(v_a_1265_);
v___x_1270_ = lean_array_push(v_implicits_1213_, v___x_1269_);
v___x_1271_ = lean_array_push(v_targets_x27_1214_, v_a_1265_);
v_type_1210_ = v___x_1266_;
v_argIdx_1211_ = v___x_1268_;
v_implicits_1213_ = v___x_1270_;
v_targets_x27_1214_ = v___x_1271_;
goto _start;
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1273_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1264_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1264_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v___x_1281_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
lean_dec(v_binderName_1225_);
v___x_1281_ = l_Lean_instInhabitedExpr;
v___x_1336_ = lean_array_get_size(v_targets_1209_);
v___x_1337_ = lean_nat_dec_lt(v_targetIdx_1212_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1338_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6);
lean_inc_ref(v_elimExpr_1241_);
v___x_1339_ = l_Lean_MessageData_ofExpr(v_elimExpr_1241_);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1342_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_dec_ref_known(v___x_1343_, 1);
v___y_1283_ = v_a_1215_;
v___y_1284_ = v_a_1216_;
v___y_1285_ = v_a_1217_;
v___y_1286_ = v_a_1218_;
goto v___jp_1282_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_binderType_1226_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
v___y_1283_ = v_a_1215_;
v___y_1284_ = v_a_1216_;
v___y_1285_ = v_a_1217_;
v___y_1286_ = v_a_1218_;
goto v___jp_1282_;
}
v___jp_1282_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_array_get_borrowed(v___x_1281_, v_targets_1209_, v_targetIdx_1212_);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v___x_1287_);
v___x_1288_ = lean_infer_type(v___x_1287_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1290_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc_n(v_a_1289_, 2);
lean_dec_ref_known(v___x_1288_, 1);
lean_inc_ref(v_binderType_1226_);
v___x_1290_ = l_Lean_Meta_isExprDefEq(v_binderType_1226_, v_a_1289_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; uint8_t v___x_1292_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1292_ = lean_unbox(v_a_1291_);
lean_dec(v_a_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = lean_box(0);
v___x_1294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0));
v___x_1295_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_1289_, v_binderType_1226_, v___x_1293_, v___x_1294_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v___x_1297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2);
lean_inc(v___x_1287_);
v___x_1298_ = l_Lean_indentExpr(v___x_1287_);
v___x_1299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1297_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v_a_1296_);
v___x_1303_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1302_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_dec_ref_known(v___x_1303_, 1);
lean_inc(v___x_1287_);
v___y_1230_ = v___x_1287_;
v___y_1231_ = v___y_1283_;
v___y_1232_ = v___y_1284_;
v___y_1233_ = v___y_1285_;
v___y_1234_ = v___y_1286_;
goto v___jp_1229_;
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1312_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1295_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1295_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_dec(v_a_1289_);
lean_dec_ref(v_binderType_1226_);
lean_inc(v___x_1287_);
v___y_1230_ = v___x_1287_;
v___y_1231_ = v___y_1283_;
v___y_1232_ = v___y_1284_;
v___y_1233_ = v___y_1285_;
v___y_1234_ = v___y_1286_;
goto v___jp_1229_;
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_a_1289_);
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_binderType_1226_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1320_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1290_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1290_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_binderType_1226_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1328_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1288_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1288_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
}
v___jp_1229_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1235_ = lean_expr_instantiate1(v_body_1227_, v___y_1230_);
lean_dec_ref(v_body_1227_);
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_nat_add(v_argIdx_1211_, v___x_1236_);
lean_dec(v_argIdx_1211_);
v___x_1238_ = lean_nat_add(v_targetIdx_1212_, v___x_1236_);
lean_dec(v_targetIdx_1212_);
v___x_1239_ = lean_array_push(v_targets_x27_1214_, v___y_1230_);
v_type_1210_ = v___x_1235_;
v_argIdx_1211_ = v___x_1237_;
v_targetIdx_1212_ = v___x_1238_;
v_targets_x27_1214_ = v___x_1239_;
v_a_1215_ = v___y_1231_;
v_a_1216_ = v___y_1232_;
v_a_1217_ = v___y_1233_;
v_a_1218_ = v___y_1234_;
goto _start;
}
}
else
{
lean_object* v___x_1352_; uint8_t v___x_1353_; 
lean_dec(v_a_1224_);
lean_dec(v_argIdx_1211_);
v___x_1352_ = lean_array_get_size(v_targets_1209_);
v___x_1353_ = lean_nat_dec_eq(v_targetIdx_1212_, v___x_1352_);
lean_dec(v_targetIdx_1212_);
if (v___x_1353_ == 0)
{
lean_object* v_elimExpr_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_elimExpr_1354_ = lean_ctor_get(v_elimInfo_1208_, 0);
lean_inc_ref(v_elimExpr_1354_);
lean_dec_ref(v_elimInfo_1208_);
v___x_1355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10);
v___x_1356_ = l_Lean_MessageData_ofExpr(v_elimExpr_1354_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1359_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_dec_ref_known(v___x_1360_, 1);
goto v___jp_1220_;
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_dec_ref(v_elimInfo_1208_);
goto v___jp_1220_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1369_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1223_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1223_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
v___jp_1220_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v_implicits_1213_);
lean_ctor_set(v___x_1221_, 1, v_targets_x27_1214_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___boxed(lean_object* v_elimInfo_1377_, lean_object* v_targets_1378_, lean_object* v_type_1379_, lean_object* v_argIdx_1380_, lean_object* v_targetIdx_1381_, lean_object* v_implicits_1382_, lean_object* v_targets_x27_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(v_elimInfo_1377_, v_targets_1378_, v_type_1379_, v_argIdx_1380_, v_targetIdx_1381_, v_implicits_1382_, v_targets_x27_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec_ref(v_targets_1378_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(lean_object* v_e_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = l_Lean_Expr_hasMVar(v_e_1390_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v_e_1390_);
return v___x_1394_;
}
else
{
lean_object* v___x_1395_; lean_object* v_mctx_1396_; lean_object* v___x_1397_; lean_object* v_fst_1398_; lean_object* v_snd_1399_; lean_object* v___x_1400_; lean_object* v_cache_1401_; lean_object* v_zetaDeltaFVarIds_1402_; lean_object* v_postponed_1403_; lean_object* v_diag_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1413_; 
v___x_1395_ = lean_st_ref_get(v___y_1391_);
v_mctx_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc_ref(v_mctx_1396_);
lean_dec(v___x_1395_);
v___x_1397_ = l_Lean_instantiateMVarsCore(v_mctx_1396_, v_e_1390_);
v_fst_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_fst_1398_);
v_snd_1399_ = lean_ctor_get(v___x_1397_, 1);
lean_inc(v_snd_1399_);
lean_dec_ref(v___x_1397_);
v___x_1400_ = lean_st_ref_take(v___y_1391_);
v_cache_1401_ = lean_ctor_get(v___x_1400_, 1);
v_zetaDeltaFVarIds_1402_ = lean_ctor_get(v___x_1400_, 2);
v_postponed_1403_ = lean_ctor_get(v___x_1400_, 3);
v_diag_1404_ = lean_ctor_get(v___x_1400_, 4);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v___x_1400_, 0);
lean_dec(v_unused_1414_);
v___x_1406_ = v___x_1400_;
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_diag_1404_);
lean_inc(v_postponed_1403_);
lean_inc(v_zetaDeltaFVarIds_1402_);
lean_inc(v_cache_1401_);
lean_dec(v___x_1400_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v_snd_1399_);
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_snd_1399_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_cache_1401_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_zetaDeltaFVarIds_1402_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v_postponed_1403_);
lean_ctor_set(v_reuseFailAlloc_1412_, 4, v_diag_1404_);
v___x_1409_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_st_ref_put(v___y_1391_, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_fst_1398_);
return v___x_1411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg___boxed(lean_object* v_e_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_e_1415_, v___y_1416_);
lean_dec(v___y_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(lean_object* v_e_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_e_1419_, v___y_1421_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___boxed(lean_object* v_e_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(v_e_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1432_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1433_, lean_object* v_i_1434_, lean_object* v_k_1435_){
_start:
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = lean_array_get_size(v_keys_1433_);
v___x_1437_ = lean_nat_dec_lt(v_i_1434_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_dec(v_i_1434_);
return v___x_1437_;
}
else
{
lean_object* v_k_x27_1438_; uint8_t v___x_1439_; 
v_k_x27_1438_ = lean_array_fget_borrowed(v_keys_1433_, v_i_1434_);
v___x_1439_ = l_Lean_instBEqMVarId_beq(v_k_1435_, v_k_x27_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = lean_nat_add(v_i_1434_, v___x_1440_);
lean_dec(v_i_1434_);
v_i_1434_ = v___x_1441_;
goto _start;
}
else
{
lean_dec(v_i_1434_);
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1443_, lean_object* v_i_1444_, lean_object* v_k_1445_){
_start:
{
uint8_t v_res_1446_; lean_object* v_r_1447_; 
v_res_1446_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1443_, v_i_1444_, v_k_1445_);
lean_dec(v_k_1445_);
lean_dec_ref(v_keys_1443_);
v_r_1447_ = lean_box(v_res_1446_);
return v_r_1447_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1448_, size_t v_x_1449_, lean_object* v_x_1450_){
_start:
{
if (lean_obj_tag(v_x_1448_) == 0)
{
lean_object* v_es_1451_; lean_object* v___x_1452_; size_t v___x_1453_; size_t v___x_1454_; lean_object* v_j_1455_; lean_object* v___x_1456_; 
v_es_1451_ = lean_ctor_get(v_x_1448_, 0);
v___x_1452_ = lean_box(2);
v___x_1453_ = ((size_t)31ULL);
v___x_1454_ = lean_usize_land(v_x_1449_, v___x_1453_);
v_j_1455_ = lean_usize_to_nat(v___x_1454_);
v___x_1456_ = lean_array_get_borrowed(v___x_1452_, v_es_1451_, v_j_1455_);
lean_dec(v_j_1455_);
switch(lean_obj_tag(v___x_1456_))
{
case 0:
{
lean_object* v_key_1457_; uint8_t v___x_1458_; 
v_key_1457_ = lean_ctor_get(v___x_1456_, 0);
v___x_1458_ = l_Lean_instBEqMVarId_beq(v_x_1450_, v_key_1457_);
return v___x_1458_;
}
case 1:
{
lean_object* v_node_1459_; size_t v___x_1460_; size_t v___x_1461_; 
v_node_1459_ = lean_ctor_get(v___x_1456_, 0);
v___x_1460_ = ((size_t)5ULL);
v___x_1461_ = lean_usize_shift_right(v_x_1449_, v___x_1460_);
v_x_1448_ = v_node_1459_;
v_x_1449_ = v___x_1461_;
goto _start;
}
default: 
{
uint8_t v___x_1463_; 
v___x_1463_ = 0;
return v___x_1463_;
}
}
}
else
{
lean_object* v_ks_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_ks_1464_ = lean_ctor_get(v_x_1448_, 0);
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1464_, v___x_1465_, v_x_1450_);
return v___x_1466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_){
_start:
{
size_t v_x_2697__boxed_1470_; uint8_t v_res_1471_; lean_object* v_r_1472_; 
v_x_2697__boxed_1470_ = lean_unbox_usize(v_x_1468_);
lean_dec(v_x_1468_);
v_res_1471_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1467_, v_x_2697__boxed_1470_, v_x_1469_);
lean_dec(v_x_1469_);
lean_dec_ref(v_x_1467_);
v_r_1472_ = lean_box(v_res_1471_);
return v_r_1472_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(lean_object* v_x_1473_, lean_object* v_x_1474_){
_start:
{
uint64_t v___x_1475_; size_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = l_Lean_instHashableMVarId_hash(v_x_1474_);
v___x_1476_ = lean_uint64_to_usize(v___x_1475_);
v___x_1477_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1473_, v___x_1476_, v_x_1474_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg___boxed(lean_object* v_x_1478_, lean_object* v_x_1479_){
_start:
{
uint8_t v_res_1480_; lean_object* v_r_1481_; 
v_res_1480_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_1478_, v_x_1479_);
lean_dec(v_x_1479_);
lean_dec_ref(v_x_1478_);
v_r_1481_ = lean_box(v_res_1480_);
return v_r_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(lean_object* v_mvarId_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v_mctx_1486_; lean_object* v_eAssignment_1487_; uint8_t v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1485_ = lean_st_ref_get(v___y_1483_);
v_mctx_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc_ref(v_mctx_1486_);
lean_dec(v___x_1485_);
v_eAssignment_1487_ = lean_ctor_get(v_mctx_1486_, 8);
lean_inc_ref(v_eAssignment_1487_);
lean_dec_ref(v_mctx_1486_);
v___x_1488_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_eAssignment_1487_, v_mvarId_1482_);
lean_dec_ref(v_eAssignment_1487_);
v___x_1489_ = lean_box(v___x_1488_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg___boxed(lean_object* v_mvarId_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_mvarId_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec(v_mvarId_1491_);
return v_res_1494_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0));
v___x_1497_ = l_Lean_stringToMessageData(v___x_1496_);
return v___x_1497_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2));
v___x_1500_ = l_Lean_stringToMessageData(v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(lean_object* v_as_1501_, size_t v_sz_1502_, size_t v_i_1503_, lean_object* v_b_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_a_1511_; uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_lt(v_i_1503_, v_sz_1502_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_b_1504_);
return v___x_1516_;
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_array_uget_borrowed(v_as_1501_, v_i_1503_);
v___x_1518_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_a_1517_, v___y_1506_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_unbox(v_a_1519_);
lean_dec(v_a_1519_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_inc(v_a_1517_);
v___x_1522_ = l_Lean_MVarId_getDecl(v_a_1517_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v_userName_1527_; uint8_t v___x_1528_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v_userName_1527_ = lean_ctor_get(v_a_1523_, 0);
lean_inc(v_userName_1527_);
lean_dec(v_a_1523_);
v___x_1528_ = l_Lean_Name_isAnonymous(v_userName_1527_);
if (v___x_1528_ == 0)
{
uint8_t v___x_1529_; 
v___x_1529_ = l_Lean_Name_hasMacroScopes(v_userName_1527_);
lean_dec(v_userName_1527_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; 
lean_inc(v_a_1517_);
v___x_1530_ = l_Lean_MVarId_getDecl(v_a_1517_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v_userName_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v_userName_1532_ = lean_ctor_get(v_a_1531_, 0);
lean_inc(v_userName_1532_);
lean_dec(v_a_1531_);
v___x_1533_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3);
v___x_1534_ = l_Lean_MessageData_ofName(v_userName_1532_);
v___x_1535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1537_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_dec_ref_known(v___x_1538_, 1);
v_a_1511_ = v___x_1520_;
goto v___jp_1510_;
}
else
{
return v___x_1538_;
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
v_a_1539_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1530_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1530_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
goto v___jp_1524_;
}
}
else
{
lean_dec(v_userName_1527_);
goto v___jp_1524_;
}
v___jp_1524_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1);
v___x_1526_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1525_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_dec_ref_known(v___x_1526_, 1);
v_a_1511_ = v___x_1520_;
goto v___jp_1510_;
}
else
{
return v___x_1526_;
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
v_a_1547_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1522_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1522_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
v_a_1511_ = v___x_1520_;
goto v___jp_1510_;
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
v_a_1555_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1518_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1518_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
v___jp_1510_:
{
size_t v___x_1512_; size_t v___x_1513_; 
v___x_1512_ = ((size_t)1ULL);
v___x_1513_ = lean_usize_add(v_i_1503_, v___x_1512_);
v_i_1503_ = v___x_1513_;
v_b_1504_ = v_a_1511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___boxed(lean_object* v_as_1563_, lean_object* v_sz_1564_, lean_object* v_i_1565_, lean_object* v_b_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
size_t v_sz_boxed_1572_; size_t v_i_boxed_1573_; lean_object* v_res_1574_; 
v_sz_boxed_1572_ = lean_unbox_usize(v_sz_1564_);
lean_dec(v_sz_1564_);
v_i_boxed_1573_ = lean_unbox_usize(v_i_1565_);
lean_dec(v_i_1565_);
v_res_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_as_1563_, v_sz_boxed_1572_, v_i_boxed_1573_, v_b_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_as_1563_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(size_t v_sz_1575_, size_t v_i_1576_, lean_object* v_bs_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_usize_dec_lt(v_i_1576_, v_sz_1575_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_bs_1577_);
return v___x_1584_;
}
else
{
lean_object* v_v_1585_; lean_object* v___x_1586_; 
v_v_1585_ = lean_array_uget_borrowed(v_bs_1577_, v_i_1576_);
lean_inc(v_v_1585_);
v___x_1586_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_v_1585_, v___y_1579_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v_bs_x27_1589_; size_t v___x_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = lean_unsigned_to_nat(0u);
v_bs_x27_1589_ = lean_array_uset(v_bs_1577_, v_i_1576_, v___x_1588_);
v___x_1590_ = ((size_t)1ULL);
v___x_1591_ = lean_usize_add(v_i_1576_, v___x_1590_);
v___x_1592_ = lean_array_uset(v_bs_x27_1589_, v_i_1576_, v_a_1587_);
v_i_1576_ = v___x_1591_;
v_bs_1577_ = v___x_1592_;
goto _start;
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v_bs_1577_);
v_a_1594_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1586_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1586_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3___boxed(lean_object* v_sz_1602_, lean_object* v_i_1603_, lean_object* v_bs_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
size_t v_sz_boxed_1610_; size_t v_i_boxed_1611_; lean_object* v_res_1612_; 
v_sz_boxed_1610_ = lean_unbox_usize(v_sz_1602_);
lean_dec(v_sz_1602_);
v_i_boxed_1611_ = lean_unbox_usize(v_i_1603_);
lean_dec(v_i_1603_);
v_res_1612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_boxed_1610_, v_i_boxed_1611_, v_bs_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object* v_elimInfo_1615_, lean_object* v_targets_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_elimType_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_elimType_1622_ = lean_ctor_get(v_elimInfo_1615_, 1);
lean_inc_ref(v_elimType_1622_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = ((lean_object*)(l_Lean_Meta_addImplicitTargets___closed__0));
v___x_1625_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(v_elimInfo_1615_, v_targets_1616_, v_elimType_1622_, v___x_1623_, v___x_1623_, v___x_1624_, v___x_1624_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v_fst_1627_; lean_object* v_snd_1628_; lean_object* v___x_1629_; size_t v_sz_1630_; size_t v___x_1631_; lean_object* v___x_1632_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v_fst_1627_ = lean_ctor_get(v_a_1626_, 0);
lean_inc(v_fst_1627_);
v_snd_1628_ = lean_ctor_get(v_a_1626_, 1);
lean_inc(v_snd_1628_);
lean_dec(v_a_1626_);
v___x_1629_ = lean_box(0);
v_sz_1630_ = lean_array_size(v_fst_1627_);
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_fst_1627_, v_sz_1630_, v___x_1631_, v___x_1629_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_fst_1627_);
if (lean_obj_tag(v___x_1632_) == 0)
{
size_t v_sz_1633_; lean_object* v___x_1634_; 
lean_dec_ref_known(v___x_1632_, 1);
v_sz_1633_ = lean_array_size(v_snd_1628_);
v___x_1634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_1633_, v___x_1631_, v_snd_1628_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
return v___x_1634_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec(v_snd_1628_);
v_a_1635_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1632_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1632_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1625_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1625_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___boxed(lean_object* v_elimInfo_1651_, lean_object* v_targets_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Meta_addImplicitTargets(v_elimInfo_1651_, v_targets_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec_ref(v_targets_1652_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(lean_object* v_mvarId_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_mvarId_1659_, v___y_1661_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___boxed(lean_object* v_mvarId_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(v_mvarId_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v_mvarId_1666_);
return v_res_1672_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(lean_object* v_00_u03b2_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_1674_, v_x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_){
_start:
{
uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_res_1680_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(v_00_u03b2_1677_, v_x_1678_, v_x_1679_);
lean_dec(v_x_1679_);
lean_dec_ref(v_x_1678_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1682_, lean_object* v_x_1683_, size_t v_x_1684_, lean_object* v_x_1685_){
_start:
{
uint8_t v___x_1686_; 
v___x_1686_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1683_, v_x_1684_, v_x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_){
_start:
{
size_t v_x_3040__boxed_1691_; uint8_t v_res_1692_; lean_object* v_r_1693_; 
v_x_3040__boxed_1691_ = lean_unbox_usize(v_x_1689_);
lean_dec(v_x_1689_);
v_res_1692_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(v_00_u03b2_1687_, v_x_1688_, v_x_3040__boxed_1691_, v_x_1690_);
lean_dec(v_x_1690_);
lean_dec_ref(v_x_1688_);
v_r_1693_ = lean_box(v_res_1692_);
return v_r_1693_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1694_, lean_object* v_keys_1695_, lean_object* v_vals_1696_, lean_object* v_heq_1697_, lean_object* v_i_1698_, lean_object* v_k_1699_){
_start:
{
uint8_t v___x_1700_; 
v___x_1700_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1695_, v_i_1698_, v_k_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1701_, lean_object* v_keys_1702_, lean_object* v_vals_1703_, lean_object* v_heq_1704_, lean_object* v_i_1705_, lean_object* v_k_1706_){
_start:
{
uint8_t v_res_1707_; lean_object* v_r_1708_; 
v_res_1707_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1701_, v_keys_1702_, v_vals_1703_, v_heq_1704_, v_i_1705_, v_k_1706_);
lean_dec(v_k_1706_);
lean_dec_ref(v_vals_1703_);
lean_dec_ref(v_keys_1702_);
v_r_1708_ = lean_box(v_res_1707_);
return v_r_1708_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
if (lean_obj_tag(v_x_1719_) == 0)
{
lean_dec(v_x_1717_);
return v_x_1718_;
}
else
{
lean_object* v_head_1720_; lean_object* v_tail_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1732_; 
v_head_1720_ = lean_ctor_get(v_x_1719_, 0);
v_tail_1721_ = lean_ctor_get(v_x_1719_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_x_1719_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1723_ = v_x_1719_;
v_isShared_1724_ = v_isSharedCheck_1732_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_tail_1721_);
lean_inc(v_head_1720_);
lean_dec(v_x_1719_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1732_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
lean_inc(v_x_1717_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 5);
lean_ctor_set(v___x_1723_, 1, v_x_1717_);
lean_ctor_set(v___x_1723_, 0, v_x_1718_);
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_x_1718_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_x_1717_);
v___x_1726_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = l_Lean_Name_reprPrec(v_head_1720_, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1726_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v_x_1718_ = v___x_1729_;
v_x_1719_ = v_tail_1721_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(lean_object* v_x_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
if (lean_obj_tag(v_x_1735_) == 0)
{
lean_dec(v_x_1733_);
return v_x_1734_;
}
else
{
lean_object* v_head_1736_; lean_object* v_tail_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1748_; 
v_head_1736_ = lean_ctor_get(v_x_1735_, 0);
v_tail_1737_ = lean_ctor_get(v_x_1735_, 1);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_x_1735_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1739_ = v_x_1735_;
v_isShared_1740_ = v_isSharedCheck_1748_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_tail_1737_);
lean_inc(v_head_1736_);
lean_dec(v_x_1735_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1748_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
lean_inc(v_x_1733_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set_tag(v___x_1739_, 5);
lean_ctor_set(v___x_1739_, 1, v_x_1733_);
lean_ctor_set(v___x_1739_, 0, v_x_1734_);
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_x_1734_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_x_1733_);
v___x_1742_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1743_ = lean_unsigned_to_nat(0u);
v___x_1744_ = l_Lean_Name_reprPrec(v_head_1736_, v___x_1743_);
v___x_1745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1742_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(v_x_1733_, v___x_1745_, v_tail_1737_);
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = l_Lean_Name_reprPrec(v___y_1749_, v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
if (lean_obj_tag(v_x_1752_) == 0)
{
lean_object* v___x_1754_; 
lean_dec(v_x_1753_);
v___x_1754_ = lean_box(0);
return v___x_1754_;
}
else
{
lean_object* v_tail_1755_; 
v_tail_1755_ = lean_ctor_get(v_x_1752_, 1);
if (lean_obj_tag(v_tail_1755_) == 0)
{
lean_object* v_head_1756_; lean_object* v___x_1757_; 
lean_dec(v_x_1753_);
v_head_1756_ = lean_ctor_get(v_x_1752_, 0);
lean_inc(v_head_1756_);
lean_dec_ref_known(v_x_1752_, 2);
v___x_1757_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_1756_);
return v___x_1757_;
}
else
{
lean_object* v_head_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_inc(v_tail_1755_);
v_head_1758_ = lean_ctor_get(v_x_1752_, 0);
lean_inc(v_head_1758_);
lean_dec_ref_known(v_x_1752_, 2);
v___x_1759_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_1758_);
v___x_1760_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(v_x_1753_, v___x_1759_, v_tail_1755_);
return v___x_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(lean_object* v_xs_1761_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1762_ = lean_array_get_size(v_xs_1761_);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_nat_dec_eq(v___x_1762_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1765_ = lean_array_to_list(v_xs_1761_);
v___x_1766_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_1767_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(v___x_1765_, v___x_1766_);
v___x_1768_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4);
v___x_1769_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5));
v___x_1770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v___x_1767_);
v___x_1771_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_1772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1768_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = l_Std_Format_fill(v___x_1773_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; 
lean_dec_ref(v_xs_1761_);
v___x_1775_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8));
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg(lean_object* v_x_1790_){
_start:
{
uint8_t v_induction_1791_; lean_object* v_typeNames_1792_; lean_object* v_elimName_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v_induction_1791_ = lean_ctor_get_uint8(v_x_1790_, sizeof(void*)*2);
v_typeNames_1792_ = lean_ctor_get(v_x_1790_, 0);
lean_inc_ref(v_typeNames_1792_);
v_elimName_1793_ = lean_ctor_get(v_x_1790_, 1);
lean_inc(v_elimName_1793_);
lean_dec_ref(v_x_1790_);
v___x_1794_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5));
v___x_1795_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2));
v___x_1796_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = l_Bool_repr___redArg(v_induction_1791_);
v___x_1799_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1796_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = 0;
v___x_1801_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*1, v___x_1800_);
v___x_1802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1795_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9));
v___x_1804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_box(1);
v___x_1806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4));
v___x_1808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___x_1794_);
v___x_1810_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_typeNames_1792_);
v___x_1811_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1796_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set_uint8(v___x_1812_, sizeof(void*)*1, v___x_1800_);
v___x_1813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1809_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_ctor_set(v___x_1814_, 1, v___x_1803_);
v___x_1815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v___x_1805_);
v___x_1816_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6));
v___x_1817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v___x_1794_);
v___x_1819_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4);
v___x_1820_ = l_Lean_Name_reprPrec(v_elimName_1793_, v___x_1797_);
v___x_1821_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set_uint8(v___x_1822_, sizeof(void*)*1, v___x_1800_);
v___x_1823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1818_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_1825_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_1826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1823_);
v___x_1827_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_1828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1824_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set_uint8(v___x_1830_, sizeof(void*)*1, v___x_1800_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr(lean_object* v_x_1831_, lean_object* v_prec_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Meta_instReprCustomEliminator_repr___redArg(v_x_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___boxed(lean_object* v_x_1834_, lean_object* v_prec_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_Meta_instReprCustomEliminator_repr(v_x_1834_, v_prec_1835_);
lean_dec(v_prec_1835_);
return v_res_1836_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_unsigned_to_nat(16u);
v___x_1841_ = lean_mk_array(v___x_1840_, v___x_1839_);
return v___x_1841_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0);
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v___x_1842_);
return v___x_1844_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2(void){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; 
v___x_1848_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3);
v___x_1849_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1);
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
v___x_1852_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(lean_object* v_f_1859_, lean_object* v_keys_1860_, lean_object* v_vals_1861_, lean_object* v_i_1862_, lean_object* v_acc_1863_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg___boxed(lean_object* v_f_1872_, lean_object* v_keys_1873_, lean_object* v_vals_1874_, lean_object* v_i_1875_, lean_object* v_acc_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_1872_, v_keys_1873_, v_vals_1874_, v_i_1875_, v_acc_1876_);
lean_dec_ref(v_vals_1874_);
lean_dec_ref(v_keys_1873_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(lean_object* v_f_1878_, lean_object* v_as_1879_, size_t v_i_1880_, size_t v_stop_1881_, lean_object* v_b_1882_){
_start:
{
lean_object* v___y_1884_; uint8_t v___x_1888_; 
v___x_1888_ = lean_usize_dec_eq(v_i_1880_, v_stop_1881_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_array_uget_borrowed(v_as_1879_, v_i_1880_);
switch(lean_obj_tag(v___x_1889_))
{
case 0:
{
lean_object* v_key_1890_; lean_object* v_val_1891_; lean_object* v___x_1892_; 
v_key_1890_ = lean_ctor_get(v___x_1889_, 0);
v_val_1891_ = lean_ctor_get(v___x_1889_, 1);
lean_inc(v_f_1878_);
lean_inc(v_val_1891_);
lean_inc(v_key_1890_);
v___x_1892_ = lean_apply_3(v_f_1878_, v_b_1882_, v_key_1890_, v_val_1891_);
v___y_1884_ = v___x_1892_;
goto v___jp_1883_;
}
case 1:
{
lean_object* v_node_1893_; lean_object* v___x_1894_; 
v_node_1893_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_f_1878_);
v___x_1894_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_1878_, v_node_1893_, v_b_1882_);
v___y_1884_ = v___x_1894_;
goto v___jp_1883_;
}
default: 
{
v___y_1884_ = v_b_1882_;
goto v___jp_1883_;
}
}
}
else
{
lean_dec(v_f_1878_);
return v_b_1882_;
}
v___jp_1883_:
{
size_t v___x_1885_; size_t v___x_1886_; 
v___x_1885_ = ((size_t)1ULL);
v___x_1886_ = lean_usize_add(v_i_1880_, v___x_1885_);
v_i_1880_ = v___x_1886_;
v_b_1882_ = v___y_1884_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_){
_start:
{
if (lean_obj_tag(v_x_1896_) == 0)
{
lean_object* v_es_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v_es_1898_ = lean_ctor_get(v_x_1896_, 0);
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_array_get_size(v_es_1898_);
v___x_1901_ = lean_nat_dec_lt(v___x_1899_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_dec(v_f_1895_);
return v_x_1897_;
}
else
{
size_t v___x_1902_; size_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = ((size_t)0ULL);
v___x_1903_ = lean_usize_of_nat(v___x_1900_);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1895_, v_es_1898_, v___x_1902_, v___x_1903_, v_x_1897_);
return v___x_1904_;
}
}
else
{
lean_object* v_ks_1905_; lean_object* v_vs_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v_ks_1905_ = lean_ctor_get(v_x_1896_, 0);
v_vs_1906_ = lean_ctor_get(v_x_1896_, 1);
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_1895_, v_ks_1905_, v_vs_1906_, v___x_1907_, v_x_1897_);
return v___x_1908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_1909_, v_x_1910_, v_x_1911_);
lean_dec_ref(v_x_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(lean_object* v_f_1913_, lean_object* v_as_1914_, lean_object* v_i_1915_, lean_object* v_stop_1916_, lean_object* v_b_1917_){
_start:
{
size_t v_i_boxed_1918_; size_t v_stop_boxed_1919_; lean_object* v_res_1920_; 
v_i_boxed_1918_ = lean_unbox_usize(v_i_1915_);
lean_dec(v_i_1915_);
v_stop_boxed_1919_ = lean_unbox_usize(v_stop_1916_);
lean_dec(v_stop_1916_);
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1913_, v_as_1914_, v_i_boxed_1918_, v_stop_boxed_1919_, v_b_1917_);
lean_dec_ref(v_as_1914_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_map_1921_, lean_object* v_f_1922_, lean_object* v_init_1923_){
_start:
{
lean_object* v___f_1924_; lean_object* v___x_1925_; 
v___f_1924_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1924_, 0, v_f_1922_);
v___x_1925_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v___f_1924_, v_map_1921_, v_init_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_map_1926_, lean_object* v_f_1927_, lean_object* v_init_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_1926_, v_f_1927_, v_init_1928_);
lean_dec_ref(v_map_1926_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1930_, lean_object* v_x_1931_, lean_object* v_x_1932_){
_start:
{
if (lean_obj_tag(v_x_1932_) == 0)
{
lean_dec(v_f_1930_);
return v_x_1931_;
}
else
{
lean_object* v_key_1933_; lean_object* v_value_1934_; lean_object* v_tail_1935_; lean_object* v___x_1936_; 
v_key_1933_ = lean_ctor_get(v_x_1932_, 0);
lean_inc(v_key_1933_);
v_value_1934_ = lean_ctor_get(v_x_1932_, 1);
lean_inc(v_value_1934_);
v_tail_1935_ = lean_ctor_get(v_x_1932_, 2);
lean_inc(v_tail_1935_);
lean_dec_ref_known(v_x_1932_, 3);
lean_inc(v_f_1930_);
v___x_1936_ = lean_apply_3(v_f_1930_, v_x_1931_, v_key_1933_, v_value_1934_);
v_x_1931_ = v___x_1936_;
v_x_1932_ = v_tail_1935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(lean_object* v_f_1938_, lean_object* v_as_1939_, size_t v_i_1940_, size_t v_stop_1941_, lean_object* v_b_1942_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = lean_usize_dec_eq(v_i_1940_, v_stop_1941_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; size_t v___x_1946_; size_t v___x_1947_; 
v___x_1944_ = lean_array_uget_borrowed(v_as_1939_, v_i_1940_);
lean_inc(v___x_1944_);
lean_inc(v_f_1938_);
v___x_1945_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_1938_, v_b_1942_, v___x_1944_);
v___x_1946_ = ((size_t)1ULL);
v___x_1947_ = lean_usize_add(v_i_1940_, v___x_1946_);
v_i_1940_ = v___x_1947_;
v_b_1942_ = v___x_1945_;
goto _start;
}
else
{
lean_dec(v_f_1938_);
return v_b_1942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_f_1949_, lean_object* v_as_1950_, lean_object* v_i_1951_, lean_object* v_stop_1952_, lean_object* v_b_1953_){
_start:
{
size_t v_i_boxed_1954_; size_t v_stop_boxed_1955_; lean_object* v_res_1956_; 
v_i_boxed_1954_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_stop_boxed_1955_ = lean_unbox_usize(v_stop_1952_);
lean_dec(v_stop_1952_);
v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1949_, v_as_1950_, v_i_boxed_1954_, v_stop_boxed_1955_, v_b_1953_);
lean_dec_ref(v_as_1950_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(lean_object* v_f_1957_, lean_object* v_init_1958_, lean_object* v_m_1959_){
_start:
{
lean_object* v_map_u2081_1960_; lean_object* v_map_u2082_1961_; lean_object* v_buckets_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_map_u2081_1960_ = lean_ctor_get(v_m_1959_, 0);
v_map_u2082_1961_ = lean_ctor_get(v_m_1959_, 1);
v_buckets_1962_ = lean_ctor_get(v_map_u2081_1960_, 1);
v___x_1963_ = lean_unsigned_to_nat(0u);
v___x_1964_ = lean_array_get_size(v_buckets_1962_);
v___x_1965_ = lean_nat_dec_lt(v___x_1963_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1961_, v_f_1957_, v_init_1958_);
return v___x_1966_;
}
else
{
size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1967_ = ((size_t)0ULL);
v___x_1968_ = lean_usize_of_nat(v___x_1964_);
lean_inc(v_f_1957_);
v___x_1969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1957_, v_buckets_1962_, v___x_1967_, v___x_1968_, v_init_1958_);
v___x_1970_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1961_, v_f_1957_, v___x_1969_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg___boxed(lean_object* v_f_1971_, lean_object* v_init_1972_, lean_object* v_m_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_1971_, v_init_1972_, v_m_1973_);
lean_dec_ref(v_m_1973_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0(lean_object* v_es_1975_, lean_object* v_a_1976_, lean_object* v_b_1977_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v_a_1976_);
lean_ctor_set(v___x_1978_, 1, v_b_1977_);
v___x_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v_es_1975_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(lean_object* v_m_1981_){
_start:
{
lean_object* v___f_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___f_1982_ = ((lean_object*)(l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0));
v___x_1983_ = lean_box(0);
v___x_1984_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v___f_1982_, v___x_1983_, v_m_1981_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___boxed(lean_object* v_m_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_m_1985_);
lean_dec_ref(v_m_1985_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_){
_start:
{
if (lean_obj_tag(v_x_1989_) == 0)
{
lean_dec(v_x_1987_);
return v_x_1988_;
}
else
{
lean_object* v_head_1990_; lean_object* v_tail_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2000_; 
v_head_1990_ = lean_ctor_get(v_x_1989_, 0);
v_tail_1991_ = lean_ctor_get(v_x_1989_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_x_1989_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1993_ = v_x_1989_;
v_isShared_1994_ = v_isSharedCheck_2000_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_tail_1991_);
lean_inc(v_head_1990_);
lean_dec(v_x_1989_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2000_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
lean_inc(v_x_1987_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 5);
lean_ctor_set(v___x_1993_, 1, v_x_1987_);
lean_ctor_set(v___x_1993_, 0, v_x_1988_);
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_x_1988_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_x_1987_);
v___x_1996_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_head_1990_);
v_x_1988_ = v___x_1997_;
v_x_1989_ = v_tail_1991_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(lean_object* v_x_2001_, lean_object* v_x_2002_){
_start:
{
if (lean_obj_tag(v_x_2001_) == 0)
{
lean_object* v___x_2003_; 
lean_dec(v_x_2002_);
v___x_2003_ = lean_box(0);
return v___x_2003_;
}
else
{
lean_object* v_tail_2004_; 
v_tail_2004_ = lean_ctor_get(v_x_2001_, 1);
if (lean_obj_tag(v_tail_2004_) == 0)
{
lean_object* v_head_2005_; 
lean_dec(v_x_2002_);
v_head_2005_ = lean_ctor_get(v_x_2001_, 0);
lean_inc(v_head_2005_);
lean_dec_ref_known(v_x_2001_, 2);
return v_head_2005_;
}
else
{
lean_object* v_head_2006_; lean_object* v___x_2007_; 
lean_inc(v_tail_2004_);
v_head_2006_ = lean_ctor_get(v_x_2001_, 0);
lean_inc(v_head_2006_);
lean_dec_ref_known(v_x_2001_, 2);
v___x_2007_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(v_x_2002_, v_head_2006_, v_tail_2004_);
return v___x_2007_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0));
v___x_2011_ = lean_string_length(v___x_2010_);
return v___x_2011_;
}
}
static lean_object* _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2);
v___x_2013_ = lean_nat_to_int(v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(lean_object* v_x_2018_){
_start:
{
lean_object* v_fst_2019_; lean_object* v_snd_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2043_; 
v_fst_2019_ = lean_ctor_get(v_x_2018_, 0);
v_snd_2020_ = lean_ctor_get(v_x_2018_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_x_2018_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2022_ = v_x_2018_;
v_isShared_2023_ = v_isSharedCheck_2043_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_snd_2020_);
lean_inc(v_fst_2019_);
lean_dec(v_x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2043_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
uint8_t v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2024_ = lean_unbox(v_fst_2019_);
lean_dec(v_fst_2019_);
v___x_2025_ = l_Bool_repr___redArg(v___x_2024_);
v___x_2026_ = lean_box(0);
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 1);
lean_ctor_set(v___x_2022_, 1, v___x_2026_);
lean_ctor_set(v___x_2022_, 0, v___x_2025_);
v___x_2028_ = v___x_2022_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2029_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_snd_2020_);
v___x_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v___x_2028_);
v___x_2031_ = l_List_reverse___redArg(v___x_2030_);
v___x_2032_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2033_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(v___x_2031_, v___x_2032_);
v___x_2034_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3);
v___x_2035_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4));
v___x_2036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v___x_2033_);
v___x_2037_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5));
v___x_2038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2034_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = 0;
v___x_2041_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*1, v___x_2040_);
return v___x_2041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(lean_object* v_x_2044_){
_start:
{
lean_object* v_fst_2045_; lean_object* v_snd_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2069_; 
v_fst_2045_ = lean_ctor_get(v_x_2044_, 0);
v_snd_2046_ = lean_ctor_get(v_x_2044_, 1);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_x_2044_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2048_ = v_x_2044_;
v_isShared_2049_ = v_isSharedCheck_2069_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_snd_2046_);
lean_inc(v_fst_2045_);
lean_dec(v_x_2044_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2069_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(v_fst_2045_);
v___x_2052_ = lean_box(0);
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 1);
lean_ctor_set(v___x_2048_, 1, v___x_2052_);
lean_ctor_set(v___x_2048_, 0, v___x_2051_);
v___x_2054_ = v___x_2048_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; 
v___x_2055_ = l_Lean_Name_reprPrec(v_snd_2046_, v___x_2050_);
v___x_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v___x_2054_);
v___x_2057_ = l_List_reverse___redArg(v___x_2056_);
v___x_2058_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2059_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(v___x_2057_, v___x_2058_);
v___x_2060_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3);
v___x_2061_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4));
v___x_2062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v___x_2059_);
v___x_2063_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5));
v___x_2064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2060_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = 0;
v___x_2067_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*1, v___x_2066_);
return v___x_2067_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(lean_object* v_x_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_){
_start:
{
if (lean_obj_tag(v_x_2072_) == 0)
{
lean_dec(v_x_2070_);
return v_x_2071_;
}
else
{
lean_object* v_head_2073_; lean_object* v_tail_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2084_; 
v_head_2073_ = lean_ctor_get(v_x_2072_, 0);
v_tail_2074_ = lean_ctor_get(v_x_2072_, 1);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_x_2072_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2076_ = v_x_2072_;
v_isShared_2077_ = v_isSharedCheck_2084_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_tail_2074_);
lean_inc(v_head_2073_);
lean_dec(v_x_2072_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2084_;
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
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_x_2071_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_x_2070_);
v___x_2079_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2073_);
v___x_2081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v_x_2071_ = v___x_2081_;
v_x_2072_ = v_tail_2074_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(lean_object* v_x_2085_, lean_object* v_x_2086_, lean_object* v_x_2087_){
_start:
{
if (lean_obj_tag(v_x_2087_) == 0)
{
lean_dec(v_x_2085_);
return v_x_2086_;
}
else
{
lean_object* v_head_2088_; lean_object* v_tail_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2099_; 
v_head_2088_ = lean_ctor_get(v_x_2087_, 0);
v_tail_2089_ = lean_ctor_get(v_x_2087_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_x_2087_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2091_ = v_x_2087_;
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_tail_2089_);
lean_inc(v_head_2088_);
lean_dec(v_x_2087_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
lean_inc(v_x_2085_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set_tag(v___x_2091_, 5);
lean_ctor_set(v___x_2091_, 1, v_x_2085_);
lean_ctor_set(v___x_2091_, 0, v_x_2086_);
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_x_2086_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_x_2085_);
v___x_2094_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2088_);
v___x_2096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(v_x_2085_, v___x_2096_, v_tail_2089_);
return v___x_2097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(lean_object* v_x_2100_, lean_object* v_x_2101_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 0)
{
lean_object* v___x_2102_; 
lean_dec(v_x_2101_);
v___x_2102_ = lean_box(0);
return v___x_2102_;
}
else
{
lean_object* v_tail_2103_; 
v_tail_2103_ = lean_ctor_get(v_x_2100_, 1);
if (lean_obj_tag(v_tail_2103_) == 0)
{
lean_object* v_head_2104_; lean_object* v___x_2105_; 
lean_dec(v_x_2101_);
v_head_2104_ = lean_ctor_get(v_x_2100_, 0);
lean_inc(v_head_2104_);
lean_dec_ref_known(v_x_2100_, 2);
v___x_2105_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2104_);
return v___x_2105_;
}
else
{
lean_object* v_head_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_inc(v_tail_2103_);
v_head_2106_ = lean_ctor_get(v_x_2100_, 0);
lean_inc(v_head_2106_);
lean_dec_ref_known(v_x_2100_, 2);
v___x_2107_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2106_);
v___x_2108_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(v_x_2101_, v___x_2107_, v_tail_2103_);
return v___x_2108_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2));
v___x_2114_ = lean_string_length(v___x_2113_);
return v___x_2114_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3, &l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3_once, _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3);
v___x_2116_ = lean_nat_to_int(v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(lean_object* v_a_2119_){
_start:
{
if (lean_obj_tag(v_a_2119_) == 0)
{
lean_object* v___x_2120_; 
v___x_2120_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1));
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2121_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2122_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(v_a_2119_, v___x_2121_);
v___x_2123_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4, &l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4);
v___x_2124_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5));
v___x_2125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___x_2122_);
v___x_2126_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_2127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2123_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = 0;
v___x_2130_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set_uint8(v___x_2130_, sizeof(void*)*1, v___x_2129_);
return v___x_2130_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_unsigned_to_nat(7u);
v___x_2141_ = lean_nat_to_int(v___x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg(lean_object* v_x_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2146_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3));
v___x_2147_ = lean_obj_once(&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4, &l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4);
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_x_2145_);
v___x_2150_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v___x_2149_);
v___x_2151_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6));
v___x_2152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Repr_addAppParen(v___x_2152_, v___x_2148_);
v___x_2154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2147_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = 0;
v___x_2156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2146_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_2159_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_2160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v___x_2157_);
v___x_2161_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_2162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2158_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
lean_ctor_set_uint8(v___x_2164_, sizeof(void*)*1, v___x_2155_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___boxed(lean_object* v_x_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_2165_);
lean_dec_ref(v_x_2165_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr(lean_object* v_x_2167_, lean_object* v_prec_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___boxed(lean_object* v_x_2170_, lean_object* v_prec_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Meta_instReprCustomEliminators_repr(v_x_2170_, v_prec_2171_);
lean_dec(v_prec_2171_);
lean_dec_ref(v_x_2170_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(lean_object* v_00_u03b2_2173_, lean_object* v_m_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_m_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___boxed(lean_object* v_00_u03b2_2176_, lean_object* v_m_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(v_00_u03b2_2176_, v_m_2177_);
lean_dec_ref(v_m_2177_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(lean_object* v_a_2179_, lean_object* v_n_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v_a_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___boxed(lean_object* v_a_2182_, lean_object* v_n_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(v_a_2182_, v_n_2183_);
lean_dec(v_n_2183_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(lean_object* v_00_u03b2_2185_, lean_object* v_00_u03c3_2186_, lean_object* v_f_2187_, lean_object* v_init_2188_, lean_object* v_m_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_2187_, v_init_2188_, v_m_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2191_, lean_object* v_00_u03c3_2192_, lean_object* v_f_2193_, lean_object* v_init_2194_, lean_object* v_m_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(v_00_u03b2_2191_, v_00_u03c3_2192_, v_f_2193_, v_init_2194_, v_m_2195_);
lean_dec_ref(v_m_2195_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(lean_object* v_x_2197_, lean_object* v_x_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_x_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___boxed(lean_object* v_x_2200_, lean_object* v_x_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(v_x_2200_, v_x_2201_);
lean_dec(v_x_2201_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2203_, lean_object* v_00_u03c3_2204_, lean_object* v_f_2205_, lean_object* v_x_2206_, lean_object* v_x_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_2205_, v_x_2206_, v_x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_2209_, lean_object* v_00_u03b2_2210_, lean_object* v_map_2211_, lean_object* v_f_2212_, lean_object* v_init_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_2211_, v_f_2212_, v_init_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_2215_, lean_object* v_00_u03b2_2216_, lean_object* v_map_2217_, lean_object* v_f_2218_, lean_object* v_init_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(v_00_u03c3_2215_, v_00_u03b2_2216_, v_map_2217_, v_f_2218_, v_init_2219_);
lean_dec_ref(v_map_2217_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2221_, lean_object* v_00_u03c3_2222_, lean_object* v_f_2223_, lean_object* v_as_2224_, size_t v_i_2225_, size_t v_stop_2226_, lean_object* v_b_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_2223_, v_as_2224_, v_i_2225_, v_stop_2226_, v_b_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2229_, lean_object* v_00_u03c3_2230_, lean_object* v_f_2231_, lean_object* v_as_2232_, lean_object* v_i_2233_, lean_object* v_stop_2234_, lean_object* v_b_2235_){
_start:
{
size_t v_i_boxed_2236_; size_t v_stop_boxed_2237_; lean_object* v_res_2238_; 
v_i_boxed_2236_ = lean_unbox_usize(v_i_2233_);
lean_dec(v_i_2233_);
v_stop_boxed_2237_ = lean_unbox_usize(v_stop_2234_);
lean_dec(v_stop_2234_);
v_res_2238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(v_00_u03b2_2229_, v_00_u03c3_2230_, v_f_2231_, v_as_2232_, v_i_boxed_2236_, v_stop_boxed_2237_, v_b_2235_);
lean_dec_ref(v_as_2232_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(lean_object* v_x_2239_, lean_object* v_x_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(v_x_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___boxed(lean_object* v_x_2242_, lean_object* v_x_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(v_x_2242_, v_x_2243_);
lean_dec(v_x_2243_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_map_2245_, lean_object* v_f_2246_, lean_object* v_init_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2246_, v_map_2245_, v_init_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_map_2249_, lean_object* v_f_2250_, lean_object* v_init_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(v_map_2249_, v_f_2250_, v_init_2251_);
lean_dec_ref(v_map_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03c3_2253_, lean_object* v_00_u03b2_2254_, lean_object* v_map_2255_, lean_object* v_f_2256_, lean_object* v_init_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2256_, v_map_2255_, v_init_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03c3_2259_, lean_object* v_00_u03b2_2260_, lean_object* v_map_2261_, lean_object* v_f_2262_, lean_object* v_init_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(v_00_u03c3_2259_, v_00_u03b2_2260_, v_map_2261_, v_f_2262_, v_init_2263_);
lean_dec_ref(v_map_2261_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_2265_, lean_object* v_00_u03b1_2266_, lean_object* v_00_u03b2_2267_, lean_object* v_f_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2268_, v_x_2269_, v_x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2272_, lean_object* v_00_u03b1_2273_, lean_object* v_00_u03b2_2274_, lean_object* v_f_2275_, lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(v_00_u03c3_2272_, v_00_u03b1_2273_, v_00_u03b2_2274_, v_f_2275_, v_x_2276_, v_x_2277_);
lean_dec_ref(v_x_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(lean_object* v_00_u03b1_2279_, lean_object* v_00_u03b2_2280_, lean_object* v_00_u03c3_2281_, lean_object* v_f_2282_, lean_object* v_as_2283_, size_t v_i_2284_, size_t v_stop_2285_, lean_object* v_b_2286_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_2282_, v_as_2283_, v_i_2284_, v_stop_2285_, v_b_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___boxed(lean_object* v_00_u03b1_2288_, lean_object* v_00_u03b2_2289_, lean_object* v_00_u03c3_2290_, lean_object* v_f_2291_, lean_object* v_as_2292_, lean_object* v_i_2293_, lean_object* v_stop_2294_, lean_object* v_b_2295_){
_start:
{
size_t v_i_boxed_2296_; size_t v_stop_boxed_2297_; lean_object* v_res_2298_; 
v_i_boxed_2296_ = lean_unbox_usize(v_i_2293_);
lean_dec(v_i_2293_);
v_stop_boxed_2297_ = lean_unbox_usize(v_stop_2294_);
lean_dec(v_stop_2294_);
v_res_2298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(v_00_u03b1_2288_, v_00_u03b2_2289_, v_00_u03c3_2290_, v_f_2291_, v_as_2292_, v_i_boxed_2296_, v_stop_boxed_2297_, v_b_2295_);
lean_dec_ref(v_as_2292_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(lean_object* v_00_u03c3_2299_, lean_object* v_00_u03b1_2300_, lean_object* v_00_u03b2_2301_, lean_object* v_f_2302_, lean_object* v_keys_2303_, lean_object* v_vals_2304_, lean_object* v_heq_2305_, lean_object* v_i_2306_, lean_object* v_acc_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_2302_, v_keys_2303_, v_vals_2304_, v_i_2306_, v_acc_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___boxed(lean_object* v_00_u03c3_2309_, lean_object* v_00_u03b1_2310_, lean_object* v_00_u03b2_2311_, lean_object* v_f_2312_, lean_object* v_keys_2313_, lean_object* v_vals_2314_, lean_object* v_heq_2315_, lean_object* v_i_2316_, lean_object* v_acc_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(v_00_u03c3_2309_, v_00_u03b1_2310_, v_00_u03b2_2311_, v_f_2312_, v_keys_2313_, v_vals_2314_, v_heq_2315_, v_i_2316_, v_acc_2317_);
lean_dec_ref(v_vals_2314_);
lean_dec_ref(v_keys_2313_);
return v_res_2318_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(lean_object* v_as_2321_, size_t v_i_2322_, size_t v_stop_2323_, uint64_t v_b_2324_){
_start:
{
uint64_t v___y_2326_; uint8_t v___x_2331_; 
v___x_2331_ = lean_usize_dec_eq(v_i_2322_, v_stop_2323_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_array_uget_borrowed(v_as_2321_, v_i_2322_);
if (lean_obj_tag(v___x_2332_) == 0)
{
uint64_t v___x_2333_; 
v___x_2333_ = 1723ULL;
v___y_2326_ = v___x_2333_;
goto v___jp_2325_;
}
else
{
uint64_t v_hash_2334_; 
v_hash_2334_ = lean_ctor_get_uint64(v___x_2332_, sizeof(void*)*2);
v___y_2326_ = v_hash_2334_;
goto v___jp_2325_;
}
}
else
{
return v_b_2324_;
}
v___jp_2325_:
{
uint64_t v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; 
v___x_2327_ = lean_uint64_mix_hash(v_b_2324_, v___y_2326_);
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_add(v_i_2322_, v___x_2328_);
v_i_2322_ = v___x_2329_;
v_b_2324_ = v___x_2327_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2335_, lean_object* v_i_2336_, lean_object* v_stop_2337_, lean_object* v_b_2338_){
_start:
{
size_t v_i_boxed_2339_; size_t v_stop_boxed_2340_; uint64_t v_b_boxed_2341_; uint64_t v_res_2342_; lean_object* v_r_2343_; 
v_i_boxed_2339_ = lean_unbox_usize(v_i_2336_);
lean_dec(v_i_2336_);
v_stop_boxed_2340_ = lean_unbox_usize(v_stop_2337_);
lean_dec(v_stop_2337_);
v_b_boxed_2341_ = lean_unbox_uint64(v_b_2338_);
lean_dec_ref(v_b_2338_);
v_res_2342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_as_2335_, v_i_boxed_2339_, v_stop_boxed_2340_, v_b_boxed_2341_);
lean_dec_ref(v_as_2335_);
v_r_2343_ = lean_box_uint64(v_res_2342_);
return v_r_2343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(lean_object* v_x_2344_, lean_object* v_x_2345_){
_start:
{
if (lean_obj_tag(v_x_2345_) == 0)
{
return v_x_2344_;
}
else
{
lean_object* v_key_2346_; lean_object* v_value_2347_; lean_object* v_tail_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2388_; 
v_key_2346_ = lean_ctor_get(v_x_2345_, 0);
v_value_2347_ = lean_ctor_get(v_x_2345_, 1);
v_tail_2348_ = lean_ctor_get(v_x_2345_, 2);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_x_2345_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2350_ = v_x_2345_;
v_isShared_2351_ = v_isSharedCheck_2388_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_tail_2348_);
lean_inc(v_value_2347_);
lean_inc(v_key_2346_);
lean_dec(v_x_2345_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2388_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v_fst_2352_; lean_object* v_snd_2353_; lean_object* v___x_2354_; uint64_t v___y_2356_; uint64_t v___y_2357_; uint64_t v___y_2377_; uint8_t v___x_2385_; 
v_fst_2352_ = lean_ctor_get(v_key_2346_, 0);
v_snd_2353_ = lean_ctor_get(v_key_2346_, 1);
v___x_2354_ = lean_array_get_size(v_x_2344_);
v___x_2385_ = lean_unbox(v_fst_2352_);
if (v___x_2385_ == 0)
{
uint64_t v___x_2386_; 
v___x_2386_ = 13ULL;
v___y_2377_ = v___x_2386_;
goto v___jp_2376_;
}
else
{
uint64_t v___x_2387_; 
v___x_2387_ = 11ULL;
v___y_2377_ = v___x_2387_;
goto v___jp_2376_;
}
v___jp_2355_:
{
uint64_t v___x_2358_; uint64_t v___x_2359_; uint64_t v___x_2360_; uint64_t v_fold_2361_; uint64_t v___x_2362_; uint64_t v___x_2363_; uint64_t v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; size_t v___x_2367_; size_t v___x_2368_; size_t v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2358_ = lean_uint64_mix_hash(v___y_2356_, v___y_2357_);
v___x_2359_ = 32ULL;
v___x_2360_ = lean_uint64_shift_right(v___x_2358_, v___x_2359_);
v_fold_2361_ = lean_uint64_xor(v___x_2358_, v___x_2360_);
v___x_2362_ = 16ULL;
v___x_2363_ = lean_uint64_shift_right(v_fold_2361_, v___x_2362_);
v___x_2364_ = lean_uint64_xor(v_fold_2361_, v___x_2363_);
v___x_2365_ = lean_uint64_to_usize(v___x_2364_);
v___x_2366_ = lean_usize_of_nat(v___x_2354_);
v___x_2367_ = ((size_t)1ULL);
v___x_2368_ = lean_usize_sub(v___x_2366_, v___x_2367_);
v___x_2369_ = lean_usize_land(v___x_2365_, v___x_2368_);
v___x_2370_ = lean_array_uget_borrowed(v_x_2344_, v___x_2369_);
lean_inc(v___x_2370_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 2, v___x_2370_);
v___x_2372_ = v___x_2350_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_key_2346_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_value_2347_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_array_uset(v_x_2344_, v___x_2369_, v___x_2372_);
v_x_2344_ = v___x_2373_;
v_x_2345_ = v_tail_2348_;
goto _start;
}
}
v___jp_2376_:
{
uint64_t v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2378_ = 7ULL;
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = lean_array_get_size(v_snd_2353_);
v___x_2381_ = lean_nat_dec_lt(v___x_2379_, v___x_2380_);
if (v___x_2381_ == 0)
{
v___y_2356_ = v___y_2377_;
v___y_2357_ = v___x_2378_;
goto v___jp_2355_;
}
else
{
size_t v___x_2382_; size_t v___x_2383_; uint64_t v___x_2384_; 
v___x_2382_ = ((size_t)0ULL);
v___x_2383_ = lean_usize_of_nat(v___x_2380_);
v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2353_, v___x_2382_, v___x_2383_, v___x_2378_);
v___y_2356_ = v___y_2377_;
v___y_2357_ = v___x_2384_;
goto v___jp_2355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_i_2389_, lean_object* v_source_2390_, lean_object* v_target_2391_){
_start:
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = lean_array_get_size(v_source_2390_);
v___x_2393_ = lean_nat_dec_lt(v_i_2389_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_dec_ref(v_source_2390_);
lean_dec(v_i_2389_);
return v_target_2391_;
}
else
{
lean_object* v_es_2394_; lean_object* v___x_2395_; lean_object* v_source_2396_; lean_object* v_target_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v_es_2394_ = lean_array_fget(v_source_2390_, v_i_2389_);
v___x_2395_ = lean_box(0);
v_source_2396_ = lean_array_fset(v_source_2390_, v_i_2389_, v___x_2395_);
v_target_2397_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(v_target_2391_, v_es_2394_);
v___x_2398_ = lean_unsigned_to_nat(1u);
v___x_2399_ = lean_nat_add(v_i_2389_, v___x_2398_);
lean_dec(v_i_2389_);
v_i_2389_ = v___x_2399_;
v_source_2390_ = v_source_2396_;
v_target_2391_ = v_target_2397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_data_2401_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v_nbuckets_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2402_ = lean_array_get_size(v_data_2401_);
v___x_2403_ = lean_unsigned_to_nat(2u);
v_nbuckets_2404_ = lean_nat_mul(v___x_2402_, v___x_2403_);
v___x_2405_ = lean_unsigned_to_nat(0u);
v___x_2406_ = lean_box(0);
v___x_2407_ = lean_mk_array(v_nbuckets_2404_, v___x_2406_);
v___x_2408_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(v___x_2405_, v_data_2401_, v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_xs_2409_, lean_object* v_ys_2410_, lean_object* v_x_2411_){
_start:
{
lean_object* v_zero_2412_; uint8_t v_isZero_2413_; 
v_zero_2412_ = lean_unsigned_to_nat(0u);
v_isZero_2413_ = lean_nat_dec_eq(v_x_2411_, v_zero_2412_);
if (v_isZero_2413_ == 1)
{
lean_dec(v_x_2411_);
return v_isZero_2413_;
}
else
{
lean_object* v_one_2414_; lean_object* v_n_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; 
v_one_2414_ = lean_unsigned_to_nat(1u);
v_n_2415_ = lean_nat_sub(v_x_2411_, v_one_2414_);
lean_dec(v_x_2411_);
v___x_2416_ = lean_array_fget_borrowed(v_xs_2409_, v_n_2415_);
v___x_2417_ = lean_array_fget_borrowed(v_ys_2410_, v_n_2415_);
v___x_2418_ = lean_name_eq(v___x_2416_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_dec(v_n_2415_);
return v___x_2418_;
}
else
{
v_x_2411_ = v_n_2415_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_xs_2420_, lean_object* v_ys_2421_, lean_object* v_x_2422_){
_start:
{
uint8_t v_res_2423_; lean_object* v_r_2424_; 
v_res_2423_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_2420_, v_ys_2421_, v_x_2422_);
lean_dec_ref(v_ys_2421_);
lean_dec_ref(v_xs_2420_);
v_r_2424_ = lean_box(v_res_2423_);
return v_r_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(lean_object* v_a_2425_, lean_object* v_b_2426_, lean_object* v_x_2427_){
_start:
{
if (lean_obj_tag(v_x_2427_) == 0)
{
lean_dec(v_b_2426_);
lean_dec_ref(v_a_2425_);
return v_x_2427_;
}
else
{
lean_object* v_key_2428_; lean_object* v_value_2429_; lean_object* v_tail_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2452_; 
v_key_2428_ = lean_ctor_get(v_x_2427_, 0);
v_value_2429_ = lean_ctor_get(v_x_2427_, 1);
v_tail_2430_ = lean_ctor_get(v_x_2427_, 2);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_x_2427_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2432_ = v_x_2427_;
v_isShared_2433_ = v_isSharedCheck_2452_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_tail_2430_);
lean_inc(v_value_2429_);
lean_inc(v_key_2428_);
lean_dec(v_x_2427_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2452_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_fst_2439_; lean_object* v_snd_2440_; lean_object* v_fst_2441_; lean_object* v_snd_2442_; uint8_t v___x_2449_; 
v_fst_2439_ = lean_ctor_get(v_key_2428_, 0);
v_snd_2440_ = lean_ctor_get(v_key_2428_, 1);
v_fst_2441_ = lean_ctor_get(v_a_2425_, 0);
v_snd_2442_ = lean_ctor_get(v_a_2425_, 1);
v___x_2449_ = lean_unbox(v_fst_2441_);
if (v___x_2449_ == 0)
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_unbox(v_fst_2439_);
if (v___x_2450_ == 0)
{
goto v___jp_2443_;
}
else
{
goto v___jp_2434_;
}
}
else
{
uint8_t v___x_2451_; 
v___x_2451_ = lean_unbox(v_fst_2439_);
if (v___x_2451_ == 0)
{
goto v___jp_2434_;
}
else
{
goto v___jp_2443_;
}
}
v___jp_2434_:
{
lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2435_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2425_, v_b_2426_, v_tail_2430_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 2, v___x_2435_);
v___x_2437_ = v___x_2432_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_key_2428_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_value_2429_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
v___jp_2443_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2444_ = lean_array_get_size(v_snd_2440_);
v___x_2445_ = lean_array_get_size(v_snd_2442_);
v___x_2446_ = lean_nat_dec_eq(v___x_2444_, v___x_2445_);
if (v___x_2446_ == 0)
{
goto v___jp_2434_;
}
else
{
uint8_t v___x_2447_; 
v___x_2447_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2440_, v_snd_2442_, v___x_2444_);
if (v___x_2447_ == 0)
{
goto v___jp_2434_;
}
else
{
lean_object* v___x_2448_; 
lean_del_object(v___x_2432_);
lean_dec(v_value_2429_);
lean_dec(v_key_2428_);
v___x_2448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2448_, 0, v_a_2425_);
lean_ctor_set(v___x_2448_, 1, v_b_2426_);
lean_ctor_set(v___x_2448_, 2, v_tail_2430_);
return v___x_2448_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(lean_object* v_a_2453_, lean_object* v_x_2454_){
_start:
{
if (lean_obj_tag(v_x_2454_) == 0)
{
uint8_t v___x_2455_; 
v___x_2455_ = 0;
return v___x_2455_;
}
else
{
lean_object* v_key_2456_; lean_object* v_tail_2457_; lean_object* v_fst_2458_; lean_object* v_snd_2459_; lean_object* v_fst_2460_; lean_object* v_snd_2461_; uint8_t v___x_2469_; 
v_key_2456_ = lean_ctor_get(v_x_2454_, 0);
v_tail_2457_ = lean_ctor_get(v_x_2454_, 2);
v_fst_2458_ = lean_ctor_get(v_key_2456_, 0);
v_snd_2459_ = lean_ctor_get(v_key_2456_, 1);
v_fst_2460_ = lean_ctor_get(v_a_2453_, 0);
v_snd_2461_ = lean_ctor_get(v_a_2453_, 1);
v___x_2469_ = lean_unbox(v_fst_2460_);
if (v___x_2469_ == 0)
{
uint8_t v___x_2470_; 
v___x_2470_ = lean_unbox(v_fst_2458_);
if (v___x_2470_ == 0)
{
goto v___jp_2462_;
}
else
{
v_x_2454_ = v_tail_2457_;
goto _start;
}
}
else
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_unbox(v_fst_2458_);
if (v___x_2472_ == 0)
{
v_x_2454_ = v_tail_2457_;
goto _start;
}
else
{
goto v___jp_2462_;
}
}
v___jp_2462_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2463_ = lean_array_get_size(v_snd_2459_);
v___x_2464_ = lean_array_get_size(v_snd_2461_);
v___x_2465_ = lean_nat_dec_eq(v___x_2463_, v___x_2464_);
if (v___x_2465_ == 0)
{
v_x_2454_ = v_tail_2457_;
goto _start;
}
else
{
uint8_t v___x_2467_; 
v___x_2467_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2459_, v_snd_2461_, v___x_2463_);
if (v___x_2467_ == 0)
{
v_x_2454_ = v_tail_2457_;
goto _start;
}
else
{
return v___x_2467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_a_2474_, lean_object* v_x_2475_){
_start:
{
uint8_t v_res_2476_; lean_object* v_r_2477_; 
v_res_2476_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2474_, v_x_2475_);
lean_dec(v_x_2475_);
lean_dec_ref(v_a_2474_);
v_r_2477_ = lean_box(v_res_2476_);
return v_r_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(lean_object* v_m_2478_, lean_object* v_a_2479_, lean_object* v_b_2480_){
_start:
{
lean_object* v_size_2481_; lean_object* v_buckets_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2542_; 
v_size_2481_ = lean_ctor_get(v_m_2478_, 0);
v_buckets_2482_ = lean_ctor_get(v_m_2478_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_m_2478_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2484_ = v_m_2478_;
v_isShared_2485_ = v_isSharedCheck_2542_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_buckets_2482_);
lean_inc(v_size_2481_);
lean_dec(v_m_2478_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2542_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v_fst_2486_; lean_object* v_snd_2487_; lean_object* v___x_2488_; uint64_t v___y_2490_; uint64_t v___y_2491_; uint64_t v___y_2531_; uint8_t v___x_2539_; 
v_fst_2486_ = lean_ctor_get(v_a_2479_, 0);
v_snd_2487_ = lean_ctor_get(v_a_2479_, 1);
v___x_2488_ = lean_array_get_size(v_buckets_2482_);
v___x_2539_ = lean_unbox(v_fst_2486_);
if (v___x_2539_ == 0)
{
uint64_t v___x_2540_; 
v___x_2540_ = 13ULL;
v___y_2531_ = v___x_2540_;
goto v___jp_2530_;
}
else
{
uint64_t v___x_2541_; 
v___x_2541_ = 11ULL;
v___y_2531_ = v___x_2541_;
goto v___jp_2530_;
}
v___jp_2489_:
{
uint64_t v___x_2492_; uint64_t v___x_2493_; uint64_t v___x_2494_; uint64_t v_fold_2495_; uint64_t v___x_2496_; uint64_t v___x_2497_; uint64_t v___x_2498_; size_t v___x_2499_; size_t v___x_2500_; size_t v___x_2501_; size_t v___x_2502_; size_t v___x_2503_; lean_object* v_bkt_2504_; uint8_t v___x_2505_; 
v___x_2492_ = lean_uint64_mix_hash(v___y_2490_, v___y_2491_);
v___x_2493_ = 32ULL;
v___x_2494_ = lean_uint64_shift_right(v___x_2492_, v___x_2493_);
v_fold_2495_ = lean_uint64_xor(v___x_2492_, v___x_2494_);
v___x_2496_ = 16ULL;
v___x_2497_ = lean_uint64_shift_right(v_fold_2495_, v___x_2496_);
v___x_2498_ = lean_uint64_xor(v_fold_2495_, v___x_2497_);
v___x_2499_ = lean_uint64_to_usize(v___x_2498_);
v___x_2500_ = lean_usize_of_nat(v___x_2488_);
v___x_2501_ = ((size_t)1ULL);
v___x_2502_ = lean_usize_sub(v___x_2500_, v___x_2501_);
v___x_2503_ = lean_usize_land(v___x_2499_, v___x_2502_);
v_bkt_2504_ = lean_array_uget_borrowed(v_buckets_2482_, v___x_2503_);
v___x_2505_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2479_, v_bkt_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v_size_x27_2507_; lean_object* v___x_2508_; lean_object* v_buckets_x27_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2506_ = lean_unsigned_to_nat(1u);
v_size_x27_2507_ = lean_nat_add(v_size_2481_, v___x_2506_);
lean_dec(v_size_2481_);
lean_inc(v_bkt_2504_);
v___x_2508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2508_, 0, v_a_2479_);
lean_ctor_set(v___x_2508_, 1, v_b_2480_);
lean_ctor_set(v___x_2508_, 2, v_bkt_2504_);
v_buckets_x27_2509_ = lean_array_uset(v_buckets_2482_, v___x_2503_, v___x_2508_);
v___x_2510_ = lean_unsigned_to_nat(4u);
v___x_2511_ = lean_nat_mul(v_size_x27_2507_, v___x_2510_);
v___x_2512_ = lean_unsigned_to_nat(3u);
v___x_2513_ = lean_nat_div(v___x_2511_, v___x_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_array_get_size(v_buckets_x27_2509_);
v___x_2515_ = lean_nat_dec_le(v___x_2513_, v___x_2514_);
lean_dec(v___x_2513_);
if (v___x_2515_ == 0)
{
lean_object* v_val_2516_; lean_object* v___x_2518_; 
v_val_2516_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(v_buckets_x27_2509_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v_val_2516_);
lean_ctor_set(v___x_2484_, 0, v_size_x27_2507_);
v___x_2518_ = v___x_2484_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_size_x27_2507_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_val_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
else
{
lean_object* v___x_2521_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v_buckets_x27_2509_);
lean_ctor_set(v___x_2484_, 0, v_size_x27_2507_);
v___x_2521_ = v___x_2484_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_size_x27_2507_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_buckets_x27_2509_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
else
{
lean_object* v___x_2523_; lean_object* v_buckets_x27_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_inc(v_bkt_2504_);
v___x_2523_ = lean_box(0);
v_buckets_x27_2524_ = lean_array_uset(v_buckets_2482_, v___x_2503_, v___x_2523_);
v___x_2525_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2479_, v_b_2480_, v_bkt_2504_);
v___x_2526_ = lean_array_uset(v_buckets_x27_2524_, v___x_2503_, v___x_2525_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v___x_2526_);
v___x_2528_ = v___x_2484_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_size_2481_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
v___jp_2530_:
{
uint64_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2532_ = 7ULL;
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = lean_array_get_size(v_snd_2487_);
v___x_2535_ = lean_nat_dec_lt(v___x_2533_, v___x_2534_);
if (v___x_2535_ == 0)
{
v___y_2490_ = v___y_2531_;
v___y_2491_ = v___x_2532_;
goto v___jp_2489_;
}
else
{
size_t v___x_2536_; size_t v___x_2537_; uint64_t v___x_2538_; 
v___x_2536_ = ((size_t)0ULL);
v___x_2537_ = lean_usize_of_nat(v___x_2534_);
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2487_, v___x_2536_, v___x_2537_, v___x_2532_);
v___y_2490_ = v___y_2531_;
v___y_2491_ = v___x_2538_;
goto v___jp_2489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_2543_, lean_object* v_x_2544_, lean_object* v_x_2545_, lean_object* v_x_2546_){
_start:
{
lean_object* v_ks_2547_; lean_object* v_vs_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2587_; 
v_ks_2547_ = lean_ctor_get(v_x_2543_, 0);
v_vs_2548_ = lean_ctor_get(v_x_2543_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_x_2543_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2550_ = v_x_2543_;
v_isShared_2551_ = v_isSharedCheck_2587_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_vs_2548_);
lean_inc(v_ks_2547_);
lean_dec(v_x_2543_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2587_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2559_ = lean_array_get_size(v_ks_2547_);
v___x_2560_ = lean_nat_dec_lt(v_x_2544_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_del_object(v___x_2550_);
lean_dec(v_x_2544_);
v___x_2561_ = lean_array_push(v_ks_2547_, v_x_2545_);
v___x_2562_ = lean_array_push(v_vs_2548_, v_x_2546_);
v___x_2563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
return v___x_2563_;
}
else
{
lean_object* v_fst_2564_; lean_object* v_snd_2565_; lean_object* v_k_x27_2566_; lean_object* v_fst_2567_; lean_object* v_snd_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2586_; 
v_fst_2564_ = lean_ctor_get(v_x_2545_, 0);
v_snd_2565_ = lean_ctor_get(v_x_2545_, 1);
v_k_x27_2566_ = lean_array_fget(v_ks_2547_, v_x_2544_);
v_fst_2567_ = lean_ctor_get(v_k_x27_2566_, 0);
v_snd_2568_ = lean_ctor_get(v_k_x27_2566_, 1);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_k_x27_2566_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2570_ = v_k_x27_2566_;
v_isShared_2571_ = v_isSharedCheck_2586_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snd_2568_);
lean_inc(v_fst_2567_);
lean_dec(v_k_x27_2566_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2586_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
uint8_t v___y_2573_; uint8_t v___x_2583_; 
v___x_2583_ = lean_unbox(v_fst_2567_);
lean_dec(v_fst_2567_);
if (v___x_2583_ == 0)
{
uint8_t v___x_2584_; 
v___x_2584_ = lean_unbox(v_fst_2564_);
if (v___x_2584_ == 0)
{
v___y_2573_ = v___x_2560_;
goto v___jp_2572_;
}
else
{
lean_del_object(v___x_2570_);
lean_dec(v_snd_2568_);
goto v___jp_2552_;
}
}
else
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_unbox(v_fst_2564_);
v___y_2573_ = v___x_2585_;
goto v___jp_2572_;
}
v___jp_2572_:
{
if (v___y_2573_ == 0)
{
lean_del_object(v___x_2570_);
lean_dec(v_snd_2568_);
goto v___jp_2552_;
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2574_ = lean_array_get_size(v_snd_2565_);
v___x_2575_ = lean_array_get_size(v_snd_2568_);
v___x_2576_ = lean_nat_dec_eq(v___x_2574_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_del_object(v___x_2570_);
lean_dec(v_snd_2568_);
goto v___jp_2552_;
}
else
{
uint8_t v___x_2577_; 
v___x_2577_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2565_, v_snd_2568_, v___x_2574_);
lean_dec(v_snd_2568_);
if (v___x_2577_ == 0)
{
lean_del_object(v___x_2570_);
goto v___jp_2552_;
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
lean_del_object(v___x_2550_);
v___x_2578_ = lean_array_fset(v_ks_2547_, v_x_2544_, v_x_2545_);
v___x_2579_ = lean_array_fset(v_vs_2548_, v_x_2544_, v_x_2546_);
lean_dec(v_x_2544_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 1);
lean_ctor_set(v___x_2570_, 1, v___x_2579_);
lean_ctor_set(v___x_2570_, 0, v___x_2578_);
v___x_2581_ = v___x_2570_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
}
}
v___jp_2552_:
{
lean_object* v___x_2554_; 
if (v_isShared_2551_ == 0)
{
v___x_2554_ = v___x_2550_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_ks_2547_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_vs_2548_);
v___x_2554_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_unsigned_to_nat(1u);
v___x_2556_ = lean_nat_add(v_x_2544_, v___x_2555_);
lean_dec(v_x_2544_);
v_x_2543_ = v___x_2554_;
v_x_2544_ = v___x_2556_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_2588_, lean_object* v_k_2589_, lean_object* v_v_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_n_2588_, v___x_2591_, v_k_2589_, v_v_2590_);
return v___x_2592_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2594_, size_t v_x_2595_, size_t v_x_2596_, lean_object* v_x_2597_, lean_object* v_x_2598_){
_start:
{
if (lean_obj_tag(v_x_2594_) == 0)
{
lean_object* v_es_2599_; size_t v___x_2600_; size_t v___x_2601_; lean_object* v_j_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v_es_2599_ = lean_ctor_get(v_x_2594_, 0);
v___x_2600_ = ((size_t)31ULL);
v___x_2601_ = lean_usize_land(v_x_2595_, v___x_2600_);
v_j_2602_ = lean_usize_to_nat(v___x_2601_);
v___x_2603_ = lean_array_get_size(v_es_2599_);
v___x_2604_ = lean_nat_dec_lt(v_j_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_dec(v_j_2602_);
lean_dec(v_x_2598_);
lean_dec_ref(v_x_2597_);
return v_x_2594_;
}
else
{
lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2656_; 
lean_inc_ref(v_es_2599_);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_x_2594_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; 
v_unused_2657_ = lean_ctor_get(v_x_2594_, 0);
lean_dec(v_unused_2657_);
v___x_2606_ = v_x_2594_;
v_isShared_2607_ = v_isSharedCheck_2656_;
goto v_resetjp_2605_;
}
else
{
lean_dec(v_x_2594_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2656_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_v_2608_; lean_object* v___x_2609_; lean_object* v_xs_x27_2610_; lean_object* v___y_2612_; 
v_v_2608_ = lean_array_fget(v_es_2599_, v_j_2602_);
v___x_2609_ = lean_box(0);
v_xs_x27_2610_ = lean_array_fset(v_es_2599_, v_j_2602_, v___x_2609_);
switch(lean_obj_tag(v_v_2608_))
{
case 0:
{
lean_object* v_key_2617_; lean_object* v_val_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2641_; 
v_key_2617_ = lean_ctor_get(v_v_2608_, 0);
v_val_2618_ = lean_ctor_get(v_v_2608_, 1);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_v_2608_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2620_ = v_v_2608_;
v_isShared_2621_ = v_isSharedCheck_2641_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_val_2618_);
lean_inc(v_key_2617_);
lean_dec(v_v_2608_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2641_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v_fst_2625_; lean_object* v_snd_2626_; lean_object* v_fst_2627_; lean_object* v_snd_2628_; uint8_t v___y_2630_; uint8_t v___x_2638_; 
v_fst_2625_ = lean_ctor_get(v_x_2597_, 0);
v_snd_2626_ = lean_ctor_get(v_x_2597_, 1);
v_fst_2627_ = lean_ctor_get(v_key_2617_, 0);
v_snd_2628_ = lean_ctor_get(v_key_2617_, 1);
v___x_2638_ = lean_unbox(v_fst_2627_);
if (v___x_2638_ == 0)
{
uint8_t v___x_2639_; 
v___x_2639_ = lean_unbox(v_fst_2625_);
if (v___x_2639_ == 0)
{
v___y_2630_ = v___x_2604_;
goto v___jp_2629_;
}
else
{
lean_del_object(v___x_2620_);
goto v___jp_2622_;
}
}
else
{
uint8_t v___x_2640_; 
v___x_2640_ = lean_unbox(v_fst_2625_);
v___y_2630_ = v___x_2640_;
goto v___jp_2629_;
}
v___jp_2622_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2617_, v_val_2618_, v_x_2597_, v_x_2598_);
v___x_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
v___y_2612_ = v___x_2624_;
goto v___jp_2611_;
}
v___jp_2629_:
{
if (v___y_2630_ == 0)
{
lean_del_object(v___x_2620_);
goto v___jp_2622_;
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2631_ = lean_array_get_size(v_snd_2626_);
v___x_2632_ = lean_array_get_size(v_snd_2628_);
v___x_2633_ = lean_nat_dec_eq(v___x_2631_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_del_object(v___x_2620_);
goto v___jp_2622_;
}
else
{
uint8_t v___x_2634_; 
v___x_2634_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2626_, v_snd_2628_, v___x_2631_);
if (v___x_2634_ == 0)
{
lean_del_object(v___x_2620_);
goto v___jp_2622_;
}
else
{
lean_object* v___x_2636_; 
lean_dec(v_val_2618_);
lean_dec(v_key_2617_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 1, v_x_2598_);
lean_ctor_set(v___x_2620_, 0, v_x_2597_);
v___x_2636_ = v___x_2620_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_x_2597_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_x_2598_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
v___y_2612_ = v___x_2636_;
goto v___jp_2611_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_node_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2654_; 
v_node_2642_ = lean_ctor_get(v_v_2608_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_v_2608_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2644_ = v_v_2608_;
v_isShared_2645_ = v_isSharedCheck_2654_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_node_2642_);
lean_dec(v_v_2608_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2654_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
size_t v___x_2646_; size_t v___x_2647_; size_t v___x_2648_; size_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2646_ = ((size_t)5ULL);
v___x_2647_ = lean_usize_shift_right(v_x_2595_, v___x_2646_);
v___x_2648_ = ((size_t)1ULL);
v___x_2649_ = lean_usize_add(v_x_2596_, v___x_2648_);
v___x_2650_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_node_2642_, v___x_2647_, v___x_2649_, v_x_2597_, v_x_2598_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2650_);
v___x_2652_ = v___x_2644_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
v___y_2612_ = v___x_2652_;
goto v___jp_2611_;
}
}
}
default: 
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v_x_2597_);
lean_ctor_set(v___x_2655_, 1, v_x_2598_);
v___y_2612_ = v___x_2655_;
goto v___jp_2611_;
}
}
v___jp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2613_ = lean_array_fset(v_xs_x27_2610_, v_j_2602_, v___y_2612_);
lean_dec(v_j_2602_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2613_);
v___x_2615_ = v___x_2606_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
lean_object* v_ks_2658_; lean_object* v_vs_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2677_; 
v_ks_2658_ = lean_ctor_get(v_x_2594_, 0);
v_vs_2659_ = lean_ctor_get(v_x_2594_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_x_2594_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2661_ = v_x_2594_;
v_isShared_2662_ = v_isSharedCheck_2677_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_vs_2659_);
lean_inc(v_ks_2658_);
lean_dec(v_x_2594_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2677_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_ks_2658_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_vs_2659_);
v___x_2664_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v_newNode_2665_; size_t v___x_2666_; uint8_t v___x_2667_; 
v_newNode_2665_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(v___x_2664_, v_x_2597_, v_x_2598_);
v___x_2666_ = ((size_t)7ULL);
v___x_2667_ = lean_usize_dec_le(v___x_2666_, v_x_2596_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2668_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2665_);
v___x_2669_ = lean_unsigned_to_nat(4u);
v___x_2670_ = lean_nat_dec_lt(v___x_2668_, v___x_2669_);
lean_dec(v___x_2668_);
if (v___x_2670_ == 0)
{
lean_object* v_ks_2671_; lean_object* v_vs_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_ks_2671_ = lean_ctor_get(v_newNode_2665_, 0);
lean_inc_ref(v_ks_2671_);
v_vs_2672_ = lean_ctor_get(v_newNode_2665_, 1);
lean_inc_ref(v_vs_2672_);
lean_dec_ref(v_newNode_2665_);
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2675_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2596_, v_ks_2671_, v_vs_2672_, v___x_2673_, v___x_2674_);
lean_dec_ref(v_vs_2672_);
lean_dec_ref(v_ks_2671_);
return v___x_2675_;
}
else
{
return v_newNode_2665_;
}
}
else
{
return v_newNode_2665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_2678_, lean_object* v_keys_2679_, lean_object* v_vals_2680_, lean_object* v_i_2681_, lean_object* v_entries_2682_){
_start:
{
lean_object* v___x_2683_; uint8_t v___x_2684_; 
v___x_2683_ = lean_array_get_size(v_keys_2679_);
v___x_2684_ = lean_nat_dec_lt(v_i_2681_, v___x_2683_);
if (v___x_2684_ == 0)
{
lean_dec(v_i_2681_);
return v_entries_2682_;
}
else
{
lean_object* v_k_2685_; lean_object* v_fst_2686_; lean_object* v_snd_2687_; lean_object* v_v_2688_; uint64_t v___y_2690_; uint64_t v___y_2691_; uint64_t v___y_2704_; uint8_t v___x_2712_; 
v_k_2685_ = lean_array_fget_borrowed(v_keys_2679_, v_i_2681_);
v_fst_2686_ = lean_ctor_get(v_k_2685_, 0);
v_snd_2687_ = lean_ctor_get(v_k_2685_, 1);
v_v_2688_ = lean_array_fget_borrowed(v_vals_2680_, v_i_2681_);
v___x_2712_ = lean_unbox(v_fst_2686_);
if (v___x_2712_ == 0)
{
uint64_t v___x_2713_; 
v___x_2713_ = 13ULL;
v___y_2704_ = v___x_2713_;
goto v___jp_2703_;
}
else
{
uint64_t v___x_2714_; 
v___x_2714_ = 11ULL;
v___y_2704_ = v___x_2714_;
goto v___jp_2703_;
}
v___jp_2689_:
{
uint64_t v___x_2692_; size_t v_h_2693_; size_t v___x_2694_; lean_object* v___x_2695_; size_t v___x_2696_; size_t v___x_2697_; size_t v___x_2698_; size_t v_h_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2692_ = lean_uint64_mix_hash(v___y_2690_, v___y_2691_);
v_h_2693_ = lean_uint64_to_usize(v___x_2692_);
v___x_2694_ = ((size_t)5ULL);
v___x_2695_ = lean_unsigned_to_nat(1u);
v___x_2696_ = ((size_t)1ULL);
v___x_2697_ = lean_usize_sub(v_depth_2678_, v___x_2696_);
v___x_2698_ = lean_usize_mul(v___x_2694_, v___x_2697_);
v_h_2699_ = lean_usize_shift_right(v_h_2693_, v___x_2698_);
v___x_2700_ = lean_nat_add(v_i_2681_, v___x_2695_);
lean_dec(v_i_2681_);
lean_inc(v_v_2688_);
lean_inc(v_k_2685_);
v___x_2701_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_entries_2682_, v_h_2699_, v_depth_2678_, v_k_2685_, v_v_2688_);
v_i_2681_ = v___x_2700_;
v_entries_2682_ = v___x_2701_;
goto _start;
}
v___jp_2703_:
{
uint64_t v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2705_ = 7ULL;
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = lean_array_get_size(v_snd_2687_);
v___x_2708_ = lean_nat_dec_lt(v___x_2706_, v___x_2707_);
if (v___x_2708_ == 0)
{
v___y_2690_ = v___y_2704_;
v___y_2691_ = v___x_2705_;
goto v___jp_2689_;
}
else
{
size_t v___x_2709_; size_t v___x_2710_; uint64_t v___x_2711_; 
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = lean_usize_of_nat(v___x_2707_);
v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2687_, v___x_2709_, v___x_2710_, v___x_2705_);
v___y_2690_ = v___y_2704_;
v___y_2691_ = v___x_2711_;
goto v___jp_2689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_2715_, lean_object* v_keys_2716_, lean_object* v_vals_2717_, lean_object* v_i_2718_, lean_object* v_entries_2719_){
_start:
{
size_t v_depth_boxed_2720_; lean_object* v_res_2721_; 
v_depth_boxed_2720_ = lean_unbox_usize(v_depth_2715_);
lean_dec(v_depth_2715_);
v_res_2721_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_2720_, v_keys_2716_, v_vals_2717_, v_i_2718_, v_entries_2719_);
lean_dec_ref(v_vals_2717_);
lean_dec_ref(v_keys_2716_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2722_, lean_object* v_x_2723_, lean_object* v_x_2724_, lean_object* v_x_2725_, lean_object* v_x_2726_){
_start:
{
size_t v_x_2108__boxed_2727_; size_t v_x_2109__boxed_2728_; lean_object* v_res_2729_; 
v_x_2108__boxed_2727_ = lean_unbox_usize(v_x_2723_);
lean_dec(v_x_2723_);
v_x_2109__boxed_2728_ = lean_unbox_usize(v_x_2724_);
lean_dec(v_x_2724_);
v_res_2729_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2722_, v_x_2108__boxed_2727_, v_x_2109__boxed_2728_, v_x_2725_, v_x_2726_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(lean_object* v_x_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_){
_start:
{
uint64_t v___y_2734_; uint64_t v___y_2735_; lean_object* v_fst_2740_; lean_object* v_snd_2741_; uint64_t v___y_2743_; uint8_t v___x_2751_; 
v_fst_2740_ = lean_ctor_get(v_x_2731_, 0);
v_snd_2741_ = lean_ctor_get(v_x_2731_, 1);
v___x_2751_ = lean_unbox(v_fst_2740_);
if (v___x_2751_ == 0)
{
uint64_t v___x_2752_; 
v___x_2752_ = 13ULL;
v___y_2743_ = v___x_2752_;
goto v___jp_2742_;
}
else
{
uint64_t v___x_2753_; 
v___x_2753_ = 11ULL;
v___y_2743_ = v___x_2753_;
goto v___jp_2742_;
}
v___jp_2733_:
{
uint64_t v___x_2736_; size_t v___x_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v___x_2736_ = lean_uint64_mix_hash(v___y_2734_, v___y_2735_);
v___x_2737_ = lean_uint64_to_usize(v___x_2736_);
v___x_2738_ = ((size_t)1ULL);
v___x_2739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2730_, v___x_2737_, v___x_2738_, v_x_2731_, v_x_2732_);
return v___x_2739_;
}
v___jp_2742_:
{
uint64_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2744_ = 7ULL;
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = lean_array_get_size(v_snd_2741_);
v___x_2747_ = lean_nat_dec_lt(v___x_2745_, v___x_2746_);
if (v___x_2747_ == 0)
{
v___y_2734_ = v___y_2743_;
v___y_2735_ = v___x_2744_;
goto v___jp_2733_;
}
else
{
size_t v___x_2748_; size_t v___x_2749_; uint64_t v___x_2750_; 
v___x_2748_ = ((size_t)0ULL);
v___x_2749_ = lean_usize_of_nat(v___x_2746_);
v___x_2750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2741_, v___x_2748_, v___x_2749_, v___x_2744_);
v___y_2734_ = v___y_2743_;
v___y_2735_ = v___x_2750_;
goto v___jp_2733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(lean_object* v_x_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_){
_start:
{
uint8_t v_stage_u2081_2757_; 
v_stage_u2081_2757_ = lean_ctor_get_uint8(v_x_2754_, sizeof(void*)*2);
if (v_stage_u2081_2757_ == 0)
{
lean_object* v_map_u2081_2758_; lean_object* v_map_u2082_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2767_; 
v_map_u2081_2758_ = lean_ctor_get(v_x_2754_, 0);
v_map_u2082_2759_ = lean_ctor_get(v_x_2754_, 1);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_x_2754_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2761_ = v_x_2754_;
v_isShared_2762_ = v_isSharedCheck_2767_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_map_u2082_2759_);
lean_inc(v_map_u2081_2758_);
lean_dec(v_x_2754_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2767_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2763_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_map_u2082_2759_, v_x_2755_, v_x_2756_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2763_);
v___x_2765_ = v___x_2761_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_map_u2081_2758_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2763_);
lean_ctor_set_uint8(v_reuseFailAlloc_2766_, sizeof(void*)*2, v_stage_u2081_2757_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
else
{
lean_object* v_map_u2081_2768_; lean_object* v_map_u2082_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2777_; 
v_map_u2081_2768_ = lean_ctor_get(v_x_2754_, 0);
v_map_u2082_2769_ = lean_ctor_get(v_x_2754_, 1);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_x_2754_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2771_ = v_x_2754_;
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_map_u2082_2769_);
lean_inc(v_map_u2081_2768_);
lean_dec(v_x_2754_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2773_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_map_u2081_2768_, v_x_2755_, v_x_2756_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2773_);
v___x_2775_ = v___x_2771_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_map_u2082_2769_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*2, v_stage_u2081_2757_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminatorEntry(lean_object* v_es_2778_, lean_object* v_e_2779_){
_start:
{
uint8_t v_induction_2780_; lean_object* v_typeNames_2781_; lean_object* v_elimName_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_induction_2780_ = lean_ctor_get_uint8(v_e_2779_, sizeof(void*)*2);
v_typeNames_2781_ = lean_ctor_get(v_e_2779_, 0);
lean_inc_ref(v_typeNames_2781_);
v_elimName_2782_ = lean_ctor_get(v_e_2779_, 1);
lean_inc(v_elimName_2782_);
lean_dec_ref(v_e_2779_);
v___x_2783_ = lean_box(v_induction_2780_);
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
lean_ctor_set(v___x_2784_, 1, v_typeNames_2781_);
v___x_2785_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(v_es_2778_, v___x_2784_, v_elimName_2782_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0(lean_object* v_00_u03b2_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_, lean_object* v_x_2789_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(v_x_2787_, v_x_2788_, v_x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(lean_object* v_00_u03b2_2791_, lean_object* v_x_2792_, lean_object* v_x_2793_, lean_object* v_x_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_x_2792_, v_x_2793_, v_x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1(lean_object* v_00_u03b2_2796_, lean_object* v_m_2797_, lean_object* v_a_2798_, lean_object* v_b_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_m_2797_, v_a_2798_, v_b_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2801_, lean_object* v_x_2802_, size_t v_x_2803_, size_t v_x_2804_, lean_object* v_x_2805_, lean_object* v_x_2806_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2802_, v_x_2803_, v_x_2804_, v_x_2805_, v_x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_, lean_object* v_x_2813_){
_start:
{
size_t v_x_2424__boxed_2814_; size_t v_x_2425__boxed_2815_; lean_object* v_res_2816_; 
v_x_2424__boxed_2814_ = lean_unbox_usize(v_x_2810_);
lean_dec(v_x_2810_);
v_x_2425__boxed_2815_ = lean_unbox_usize(v_x_2811_);
lean_dec(v_x_2811_);
v_res_2816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(v_00_u03b2_2808_, v_x_2809_, v_x_2424__boxed_2814_, v_x_2425__boxed_2815_, v_x_2812_, v_x_2813_);
return v_res_2816_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2817_, lean_object* v_a_2818_, lean_object* v_x_2819_){
_start:
{
uint8_t v___x_2820_; 
v___x_2820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2818_, v_x_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2821_, lean_object* v_a_2822_, lean_object* v_x_2823_){
_start:
{
uint8_t v_res_2824_; lean_object* v_r_2825_; 
v_res_2824_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(v_00_u03b2_2821_, v_a_2822_, v_x_2823_);
lean_dec(v_x_2823_);
lean_dec_ref(v_a_2822_);
v_r_2825_ = lean_box(v_res_2824_);
return v_r_2825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2826_, lean_object* v_data_2827_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(v_data_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_2829_, lean_object* v_a_2830_, lean_object* v_b_2831_, lean_object* v_x_2832_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2830_, v_b_2831_, v_x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_xs_2834_, lean_object* v_ys_2835_, lean_object* v_hsz_2836_, lean_object* v_x_2837_, lean_object* v_x_2838_){
_start:
{
uint8_t v___x_2839_; 
v___x_2839_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_2834_, v_ys_2835_, v_x_2837_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_xs_2840_, lean_object* v_ys_2841_, lean_object* v_hsz_2842_, lean_object* v_x_2843_, lean_object* v_x_2844_){
_start:
{
uint8_t v_res_2845_; lean_object* v_r_2846_; 
v_res_2845_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(v_xs_2840_, v_ys_2841_, v_hsz_2842_, v_x_2843_, v_x_2844_);
lean_dec_ref(v_ys_2841_);
lean_dec_ref(v_xs_2840_);
v_r_2846_ = lean_box(v_res_2845_);
return v_r_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2847_, lean_object* v_n_2848_, lean_object* v_k_2849_, lean_object* v_v_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_n_2848_, v_k_2849_, v_v_2850_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2852_, size_t v_depth_2853_, lean_object* v_keys_2854_, lean_object* v_vals_2855_, lean_object* v_heq_2856_, lean_object* v_i_2857_, lean_object* v_entries_2858_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_2853_, v_keys_2854_, v_vals_2855_, v_i_2857_, v_entries_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2860_, lean_object* v_depth_2861_, lean_object* v_keys_2862_, lean_object* v_vals_2863_, lean_object* v_heq_2864_, lean_object* v_i_2865_, lean_object* v_entries_2866_){
_start:
{
size_t v_depth_boxed_2867_; lean_object* v_res_2868_; 
v_depth_boxed_2867_ = lean_unbox_usize(v_depth_2861_);
lean_dec(v_depth_2861_);
v_res_2868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_2860_, v_depth_boxed_2867_, v_keys_2862_, v_vals_2863_, v_heq_2864_, v_i_2865_, v_entries_2866_);
lean_dec_ref(v_vals_2863_);
lean_dec_ref(v_keys_2862_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03b2_2869_, lean_object* v_i_2870_, lean_object* v_source_2871_, lean_object* v_target_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(v_i_2870_, v_source_2871_, v_target_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2874_, lean_object* v_x_2875_, lean_object* v_x_2876_, lean_object* v_x_2877_, lean_object* v_x_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_x_2875_, v_x_2876_, v_x_2877_, v_x_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(v_x_2881_, v_x_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_2884_){
_start:
{
uint8_t v_stage_u2081_2885_; 
v_stage_u2081_2885_ = lean_ctor_get_uint8(v_m_2884_, sizeof(void*)*2);
if (v_stage_u2081_2885_ == 0)
{
return v_m_2884_;
}
else
{
lean_object* v_map_u2081_2886_; lean_object* v_map_u2082_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2895_; 
v_map_u2081_2886_ = lean_ctor_get(v_m_2884_, 0);
v_map_u2082_2887_ = lean_ctor_get(v_m_2884_, 1);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_m_2884_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2889_ = v_m_2884_;
v_isShared_2890_ = v_isSharedCheck_2895_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_map_u2082_2887_);
lean_inc(v_map_u2081_2886_);
lean_dec(v_m_2884_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2895_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
uint8_t v___x_2891_; lean_object* v___x_2893_; 
v___x_2891_ = 0;
if (v_isShared_2890_ == 0)
{
v___x_2893_ = v___x_2889_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_map_u2081_2886_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_map_u2082_2887_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_ctor_set_uint8(v___x_2893_, sizeof(void*)*2, v___x_2891_);
return v___x_2893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_2896_, lean_object* v_m_2897_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(v_m_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(lean_object* v_x_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v_a_2900_);
lean_inc_ref_n(v___x_2901_, 2);
v___x_2902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
lean_ctor_set(v___x_2902_, 2, v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object* v_x_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(v_x_2903_, v_a_2904_);
lean_dec_ref(v_x_2903_);
return v_res_2905_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2916_; lean_object* v___f_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___f_2916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___f_2917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2918_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4);
v___x_2919_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
lean_ctor_set(v___x_2921_, 1, v___x_2919_);
lean_ctor_set(v___x_2921_, 2, v___x_2918_);
lean_ctor_set(v___x_2921_, 3, v___f_2917_);
lean_ctor_set(v___x_2921_, 4, v___f_2916_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_);
v___x_2924_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object* v_a_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
return v_res_2926_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(lean_object* v_x_2927_){
_start:
{
uint8_t v___x_2928_; 
v___x_2928_ = 0;
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed(lean_object* v_x_2929_){
_start:
{
uint8_t v_res_2930_; lean_object* v_r_2931_; 
v_res_2930_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(v_x_2929_);
lean_dec(v_x_2929_);
v_r_2931_ = lean_box(v_res_2930_);
return v_r_2931_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(lean_object* v_fvarId_2932_, lean_object* v_x_2933_){
_start:
{
uint8_t v___x_2934_; 
v___x_2934_ = l_Lean_instBEqFVarId_beq(v_fvarId_2932_, v_x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_2935_, lean_object* v_x_2936_){
_start:
{
uint8_t v_res_2937_; lean_object* v_r_2938_; 
v_res_2937_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(v_fvarId_2935_, v_x_2936_);
lean_dec(v_x_2936_);
lean_dec(v_fvarId_2935_);
v_r_2938_ = lean_box(v_res_2937_);
return v_r_2938_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = lean_box(0);
v___x_2941_ = lean_unsigned_to_nat(16u);
v___x_2942_ = lean_mk_array(v___x_2941_, v___x_2940_);
return v___x_2942_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2943_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1);
v___x_2944_ = lean_unsigned_to_nat(0u);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
lean_ctor_set(v___x_2945_, 1, v___x_2943_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(lean_object* v_e_2946_, lean_object* v_fvarId_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v___x_2950_; uint8_t v_fst_2952_; lean_object* v_mctx_2953_; lean_object* v___y_2971_; lean_object* v_mctx_2976_; lean_object* v___f_2977_; lean_object* v___f_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2950_ = lean_st_ref_get(v___y_2948_);
v_mctx_2976_ = lean_ctor_get(v___x_2950_, 0);
lean_inc_ref_n(v_mctx_2976_, 2);
lean_dec(v___x_2950_);
v___f_2977_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0));
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2978_, 0, v_fvarId_2947_);
v___x_2979_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2);
v___x_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
lean_ctor_set(v___x_2980_, 1, v_mctx_2976_);
v___x_2981_ = l_Lean_Expr_hasFVar(v_e_2946_);
if (v___x_2981_ == 0)
{
uint8_t v___x_2982_; 
v___x_2982_ = l_Lean_Expr_hasMVar(v_e_2946_);
if (v___x_2982_ == 0)
{
lean_dec_ref_known(v___x_2980_, 2);
lean_dec_ref(v___f_2978_);
lean_dec_ref(v_e_2946_);
v_fst_2952_ = v___x_2982_;
v_mctx_2953_ = v_mctx_2976_;
goto v___jp_2951_;
}
else
{
lean_object* v___x_2983_; 
lean_dec_ref(v_mctx_2976_);
v___x_2983_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2978_, v___f_2977_, v_e_2946_, v___x_2980_);
v___y_2971_ = v___x_2983_;
goto v___jp_2970_;
}
}
else
{
lean_object* v___x_2984_; 
lean_dec_ref(v_mctx_2976_);
v___x_2984_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2978_, v___f_2977_, v_e_2946_, v___x_2980_);
v___y_2971_ = v___x_2984_;
goto v___jp_2970_;
}
v___jp_2951_:
{
lean_object* v___x_2954_; lean_object* v_cache_2955_; lean_object* v_zetaDeltaFVarIds_2956_; lean_object* v_postponed_2957_; lean_object* v_diag_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2968_; 
v___x_2954_ = lean_st_ref_take(v___y_2948_);
v_cache_2955_ = lean_ctor_get(v___x_2954_, 1);
v_zetaDeltaFVarIds_2956_ = lean_ctor_get(v___x_2954_, 2);
v_postponed_2957_ = lean_ctor_get(v___x_2954_, 3);
v_diag_2958_ = lean_ctor_get(v___x_2954_, 4);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v___x_2954_, 0);
lean_dec(v_unused_2969_);
v___x_2960_ = v___x_2954_;
v_isShared_2961_ = v_isSharedCheck_2968_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_diag_2958_);
lean_inc(v_postponed_2957_);
lean_inc(v_zetaDeltaFVarIds_2956_);
lean_inc(v_cache_2955_);
lean_dec(v___x_2954_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2968_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v_mctx_2953_);
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_mctx_2953_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_cache_2955_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v_zetaDeltaFVarIds_2956_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v_postponed_2957_);
lean_ctor_set(v_reuseFailAlloc_2967_, 4, v_diag_2958_);
v___x_2963_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = lean_st_ref_put(v___y_2948_, v___x_2963_);
v___x_2965_ = lean_box(v_fst_2952_);
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
return v___x_2966_;
}
}
}
v___jp_2970_:
{
lean_object* v_snd_2972_; lean_object* v_fst_2973_; lean_object* v_mctx_2974_; uint8_t v___x_2975_; 
v_snd_2972_ = lean_ctor_get(v___y_2971_, 1);
lean_inc(v_snd_2972_);
v_fst_2973_ = lean_ctor_get(v___y_2971_, 0);
lean_inc(v_fst_2973_);
lean_dec_ref(v___y_2971_);
v_mctx_2974_ = lean_ctor_get(v_snd_2972_, 1);
lean_inc_ref(v_mctx_2974_);
lean_dec(v_snd_2972_);
v___x_2975_ = lean_unbox(v_fst_2973_);
lean_dec(v_fst_2973_);
v_fst_2952_ = v___x_2975_;
v_mctx_2953_ = v_mctx_2974_;
goto v___jp_2951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___boxed(lean_object* v_e_2985_, lean_object* v_fvarId_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_e_2985_, v_fvarId_2986_, v___y_2987_);
lean_dec(v___y_2987_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(lean_object* v_e_2990_, lean_object* v_fvarId_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_e_2990_, v_fvarId_2991_, v___y_2993_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___boxed(lean_object* v_e_2998_, lean_object* v_fvarId_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(v_e_2998_, v_fvarId_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(lean_object* v_upperBound_3009_, lean_object* v___x_3010_, lean_object* v_xs_3011_, lean_object* v___x_3012_, lean_object* v_a_3013_, lean_object* v_b_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
uint8_t v___x_3020_; 
v___x_3020_ = lean_nat_dec_lt(v_a_3013_, v_upperBound_3009_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; 
lean_dec(v_a_3013_);
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_b_3014_);
return v___x_3021_;
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_dec_ref(v_b_3014_);
v___x_3022_ = l_Lean_instInhabitedExpr;
v___x_3023_ = lean_array_fget_borrowed(v___x_3010_, v_a_3013_);
v___x_3024_ = lean_array_get_borrowed(v___x_3022_, v_xs_3011_, v___x_3023_);
lean_inc(v___y_3018_);
lean_inc_ref(v___y_3017_);
lean_inc(v___y_3016_);
lean_inc_ref(v___y_3015_);
lean_inc(v___x_3024_);
v___x_3025_ = lean_infer_type(v___x_3024_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
v___x_3027_ = l_Lean_Expr_fvarId_x21(v___x_3012_);
v___x_3028_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_a_3026_, v___x_3027_, v___y_3016_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3045_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3045_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3045_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = lean_box(0);
v___x_3034_ = lean_unbox(v_a_3029_);
lean_dec(v_a_3029_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_del_object(v___x_3031_);
v___x_3035_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0));
v___x_3036_ = lean_unsigned_to_nat(1u);
v___x_3037_ = lean_nat_add(v_a_3013_, v___x_3036_);
lean_dec(v_a_3013_);
v_a_3013_ = v___x_3037_;
v_b_3014_ = v___x_3035_;
goto _start;
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
lean_dec(v_a_3013_);
v___x_3039_ = lean_box(v___x_3020_);
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
lean_ctor_set(v___x_3041_, 1, v___x_3033_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3041_);
v___x_3043_ = v___x_3031_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec(v_a_3013_);
v_a_3046_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3028_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3028_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec(v_a_3013_);
v_a_3054_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3025_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3025_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___boxed(lean_object* v_upperBound_3062_, lean_object* v___x_3063_, lean_object* v_xs_3064_, lean_object* v___x_3065_, lean_object* v_a_3066_, lean_object* v_b_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v_upperBound_3062_, v___x_3063_, v_xs_3064_, v___x_3065_, v_a_3066_, v_b_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec_ref(v___x_3065_);
lean_dec_ref(v_xs_3064_);
lean_dec_ref(v___x_3063_);
lean_dec(v_upperBound_3062_);
return v_res_3073_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0));
v___x_3076_ = l_Lean_stringToMessageData(v___x_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(lean_object* v_upperBound_3077_, lean_object* v___x_3078_, lean_object* v___x_3079_, lean_object* v_xs_3080_, lean_object* v_a_3081_, lean_object* v_b_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_a_3089_; uint8_t v___x_3093_; 
v___x_3093_ = lean_nat_dec_lt(v_a_3081_, v_upperBound_3077_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; 
lean_dec(v_a_3081_);
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v_b_3082_);
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3095_ = l_Lean_instInhabitedExpr;
v___x_3096_ = lean_unsigned_to_nat(1u);
v___x_3097_ = lean_nat_add(v_a_3081_, v___x_3096_);
v___x_3098_ = lean_array_fget_borrowed(v___x_3079_, v_a_3081_);
v___x_3099_ = lean_array_get_borrowed(v___x_3095_, v_xs_3080_, v___x_3098_);
v___x_3126_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0));
v___x_3127_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v___x_3078_, v___x_3079_, v_xs_3080_, v___x_3099_, v___x_3097_, v___x_3126_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v_fst_3129_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v_fst_3129_ = lean_ctor_get(v_a_3128_, 0);
lean_inc(v_fst_3129_);
lean_dec(v_a_3128_);
if (lean_obj_tag(v_fst_3129_) == 0)
{
goto v___jp_3100_;
}
else
{
lean_object* v_val_3130_; uint8_t v___x_3131_; 
v_val_3130_ = lean_ctor_get(v_fst_3129_, 0);
lean_inc(v_val_3130_);
lean_dec_ref_known(v_fst_3129_, 1);
v___x_3131_ = lean_unbox(v_val_3130_);
lean_dec(v_val_3130_);
if (v___x_3131_ == 0)
{
goto v___jp_3100_;
}
else
{
v_a_3089_ = v_b_3082_;
goto v___jp_3088_;
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v_b_3082_);
lean_dec(v_a_3081_);
v_a_3132_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3127_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3127_);
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
v___jp_3100_:
{
lean_object* v___x_3101_; 
lean_inc(v___y_3086_);
lean_inc_ref(v___y_3085_);
lean_inc(v___y_3084_);
lean_inc_ref(v___y_3083_);
lean_inc(v___x_3099_);
v___x_3101_ = lean_infer_type(v___x_3099_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v___x_3103_ = l_Lean_Expr_getAppFn(v_a_3102_);
if (lean_obj_tag(v___x_3103_) == 4)
{
lean_object* v_declName_3104_; lean_object* v___x_3105_; 
lean_dec(v_a_3102_);
v_declName_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_declName_3104_);
lean_dec_ref_known(v___x_3103_, 2);
v___x_3105_ = lean_array_push(v_b_3082_, v_declName_3104_);
v_a_3089_ = v___x_3105_;
goto v___jp_3088_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_dec_ref(v___x_3103_);
v___x_3106_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1);
v___x_3107_ = l_Lean_indentExpr(v_a_3102_);
v___x_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_3108_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_dec_ref_known(v___x_3109_, 1);
v_a_3089_ = v_b_3082_;
goto v___jp_3088_;
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec_ref(v_b_3082_);
lean_dec(v_a_3081_);
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v_b_3082_);
lean_dec(v_a_3081_);
v_a_3118_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3101_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3101_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
v___jp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_unsigned_to_nat(1u);
v___x_3091_ = lean_nat_add(v_a_3081_, v___x_3090_);
lean_dec(v_a_3081_);
v_a_3081_ = v___x_3091_;
v_b_3082_ = v_a_3089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___boxed(lean_object* v_upperBound_3140_, lean_object* v___x_3141_, lean_object* v___x_3142_, lean_object* v_xs_3143_, lean_object* v_a_3144_, lean_object* v_b_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v_upperBound_3140_, v___x_3141_, v___x_3142_, v_xs_3143_, v_a_3144_, v_b_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_xs_3143_);
lean_dec_ref(v___x_3142_);
lean_dec(v___x_3141_);
lean_dec(v_upperBound_3140_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0(lean_object* v_a_3152_, uint8_t v_induction_3153_, lean_object* v_elimName_3154_, lean_object* v_xs_3155_, lean_object* v_x_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_targetsPos_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v_targetsPos_3162_ = lean_ctor_get(v_a_3152_, 3);
v___x_3163_ = lean_array_get_size(v_targetsPos_3162_);
v___x_3164_ = lean_unsigned_to_nat(0u);
v___x_3165_ = ((lean_object*)(l_Lean_Meta_addImplicitTargets___closed__0));
v___x_3166_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v___x_3163_, v___x_3163_, v_targetsPos_3162_, v_xs_3155_, v___x_3164_, v___x_3165_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3175_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3175_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3175_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3171_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3171_, 0, v_a_3167_);
lean_ctor_set(v___x_3171_, 1, v_elimName_3154_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*2, v_induction_3153_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v___x_3171_);
v___x_3173_ = v___x_3169_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec(v_elimName_3154_);
v_a_3176_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3166_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3166_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0___boxed(lean_object* v_a_3184_, lean_object* v_induction_3185_, lean_object* v_elimName_3186_, lean_object* v_xs_3187_, lean_object* v_x_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v_induction_boxed_3194_; lean_object* v_res_3195_; 
v_induction_boxed_3194_ = lean_unbox(v_induction_3185_);
v_res_3195_ = l_Lean_Meta_mkCustomEliminator___lam__0(v_a_3184_, v_induction_boxed_3194_, v_elimName_3186_, v_xs_3187_, v_x_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec_ref(v_x_3188_);
lean_dec_ref(v_xs_3187_);
lean_dec_ref(v_a_3184_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(lean_object* v_ref_3196_, lean_object* v_msg_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_toCold_3203_; lean_object* v_currRecDepth_3204_; lean_object* v_ref_3205_; uint8_t v_diag_3206_; uint8_t v_suppressElabErrors_3207_; lean_object* v_ref_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v_toCold_3203_ = lean_ctor_get(v___y_3200_, 0);
v_currRecDepth_3204_ = lean_ctor_get(v___y_3200_, 1);
v_ref_3205_ = lean_ctor_get(v___y_3200_, 2);
v_diag_3206_ = lean_ctor_get_uint8(v___y_3200_, sizeof(void*)*3);
v_suppressElabErrors_3207_ = lean_ctor_get_uint8(v___y_3200_, sizeof(void*)*3 + 1);
v_ref_3208_ = l_Lean_replaceRef(v_ref_3196_, v_ref_3205_);
lean_inc(v_currRecDepth_3204_);
lean_inc_ref(v_toCold_3203_);
v___x_3209_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3209_, 0, v_toCold_3203_);
lean_ctor_set(v___x_3209_, 1, v_currRecDepth_3204_);
lean_ctor_set(v___x_3209_, 2, v_ref_3208_);
lean_ctor_set_uint8(v___x_3209_, sizeof(void*)*3, v_diag_3206_);
lean_ctor_set_uint8(v___x_3209_, sizeof(void*)*3 + 1, v_suppressElabErrors_3207_);
v___x_3210_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_3197_, v___y_3198_, v___y_3199_, v___x_3209_, v___y_3201_);
lean_dec_ref_known(v___x_3209_, 3);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3211_, lean_object* v_msg_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3211_, v_msg_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v_ref_3211_);
return v_res_3218_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3219_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
return v___x_3221_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3222_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3223_ = lean_unsigned_to_nat(0u);
v___x_3224_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
lean_ctor_set(v___x_3224_, 2, v___x_3223_);
lean_ctor_set(v___x_3224_, 3, v___x_3223_);
lean_ctor_set(v___x_3224_, 4, v___x_3222_);
lean_ctor_set(v___x_3224_, 5, v___x_3222_);
lean_ctor_set(v___x_3224_, 6, v___x_3222_);
lean_ctor_set(v___x_3224_, 7, v___x_3222_);
lean_ctor_set(v___x_3224_, 8, v___x_3222_);
lean_ctor_set(v___x_3224_, 9, v___x_3222_);
lean_ctor_set(v___x_3224_, 10, v___x_3222_);
return v___x_3224_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3225_ = lean_unsigned_to_nat(32u);
v___x_3226_ = lean_mk_empty_array_with_capacity(v___x_3225_);
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
return v___x_3227_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3228_ = ((size_t)5ULL);
v___x_3229_ = lean_unsigned_to_nat(0u);
v___x_3230_ = lean_unsigned_to_nat(32u);
v___x_3231_ = lean_mk_empty_array_with_capacity(v___x_3230_);
v___x_3232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3233_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
lean_ctor_set(v___x_3233_, 1, v___x_3231_);
lean_ctor_set(v___x_3233_, 2, v___x_3229_);
lean_ctor_set(v___x_3233_, 3, v___x_3229_);
lean_ctor_set_usize(v___x_3233_, 4, v___x_3228_);
return v___x_3233_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3234_ = lean_box(1);
v___x_3235_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_3236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
lean_ctor_set(v___x_3237_, 1, v___x_3235_);
lean_ctor_set(v___x_3237_, 2, v___x_3234_);
return v___x_3237_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_3240_ = l_Lean_stringToMessageData(v___x_3239_);
return v___x_3240_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_3243_ = l_Lean_stringToMessageData(v___x_3242_);
return v___x_3243_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_3246_ = l_Lean_stringToMessageData(v___x_3245_);
return v___x_3246_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_3255_ = l_Lean_stringToMessageData(v___x_3254_);
return v___x_3255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_3258_ = l_Lean_stringToMessageData(v___x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3259_, lean_object* v_declHint_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v___x_3263_; lean_object* v_env_3264_; uint8_t v___x_3265_; 
v___x_3263_ = lean_st_ref_get(v___y_3261_);
v_env_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc_ref(v_env_3264_);
lean_dec(v___x_3263_);
v___x_3265_ = l_Lean_Name_isAnonymous(v_declHint_3260_);
if (v___x_3265_ == 0)
{
uint8_t v_isExporting_3266_; 
v_isExporting_3266_ = lean_ctor_get_uint8(v_env_3264_, sizeof(void*)*8);
if (v_isExporting_3266_ == 0)
{
lean_object* v___x_3267_; 
lean_dec_ref(v_env_3264_);
lean_dec(v_declHint_3260_);
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v_msg_3259_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; uint8_t v___x_3269_; 
lean_inc_ref(v_env_3264_);
v___x_3268_ = l_Lean_Environment_setExporting(v_env_3264_, v___x_3265_);
lean_inc(v_declHint_3260_);
lean_inc_ref(v___x_3268_);
v___x_3269_ = l_Lean_Environment_contains(v___x_3268_, v_declHint_3260_, v_isExporting_3266_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; 
lean_dec_ref(v___x_3268_);
lean_dec_ref(v_env_3264_);
lean_dec(v_declHint_3260_);
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v_msg_3259_);
return v___x_3270_;
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v_c_3276_; lean_object* v___x_3277_; 
v___x_3271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_3272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_3273_ = l_Lean_Options_empty;
v___x_3274_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3268_);
lean_ctor_set(v___x_3274_, 1, v___x_3271_);
lean_ctor_set(v___x_3274_, 2, v___x_3272_);
lean_ctor_set(v___x_3274_, 3, v___x_3273_);
lean_inc(v_declHint_3260_);
v___x_3275_ = l_Lean_MessageData_ofConstName(v_declHint_3260_, v___x_3265_);
v_c_3276_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3276_, 0, v___x_3274_);
lean_ctor_set(v_c_3276_, 1, v___x_3275_);
v___x_3277_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3264_, v_declHint_3260_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
lean_dec_ref(v_env_3264_);
lean_dec(v_declHint_3260_);
v___x_3278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v_c_3276_);
v___x_3280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = l_Lean_MessageData_note(v___x_3281_);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v_msg_3259_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
return v___x_3284_;
}
else
{
lean_object* v_val_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3320_; 
v_val_3285_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3287_ = v___x_3277_;
v_isShared_3288_ = v_isSharedCheck_3320_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_val_3285_);
lean_dec(v___x_3277_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3320_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v_mod_3292_; uint8_t v___x_3293_; 
v___x_3289_ = lean_box(0);
v___x_3290_ = l_Lean_Environment_header(v_env_3264_);
lean_dec_ref(v_env_3264_);
v___x_3291_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3290_);
v_mod_3292_ = lean_array_get(v___x_3289_, v___x_3291_, v_val_3285_);
lean_dec(v_val_3285_);
lean_dec_ref(v___x_3291_);
v___x_3293_ = l_Lean_isPrivateName(v_declHint_3260_);
lean_dec(v_declHint_3260_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3305_; 
v___x_3294_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
lean_ctor_set(v___x_3295_, 1, v_c_3276_);
v___x_3296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = l_Lean_MessageData_ofName(v_mod_3292_);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3299_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = l_Lean_MessageData_note(v___x_3301_);
v___x_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3303_, 0, v_msg_3259_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
if (v_isShared_3288_ == 0)
{
lean_ctor_set_tag(v___x_3287_, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3303_);
v___x_3305_ = v___x_3287_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3307_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
lean_ctor_set(v___x_3308_, 1, v_c_3276_);
v___x_3309_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = l_Lean_MessageData_ofName(v_mod_3292_);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = l_Lean_MessageData_note(v___x_3314_);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v_msg_3259_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
if (v_isShared_3288_ == 0)
{
lean_ctor_set_tag(v___x_3287_, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3316_);
v___x_3318_ = v___x_3287_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3321_; 
lean_dec_ref(v_env_3264_);
lean_dec(v_declHint_3260_);
v___x_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3321_, 0, v_msg_3259_);
return v___x_3321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3322_, lean_object* v_declHint_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3322_, v_declHint_3323_, v___y_3324_);
lean_dec(v___y_3324_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_3327_, lean_object* v_declHint_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___x_3334_; lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3344_; 
v___x_3334_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3327_, v_declHint_3328_, v___y_3332_);
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3344_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3344_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3339_ = l_Lean_unknownIdentifierMessageTag;
v___x_3340_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
lean_ctor_set(v___x_3340_, 1, v_a_3335_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3340_);
v___x_3342_ = v___x_3337_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_3345_, lean_object* v_declHint_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_3345_, v_declHint_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_ref_3353_, lean_object* v_msg_3354_, lean_object* v_declHint_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; lean_object* v_a_3362_; lean_object* v___x_3363_; 
v___x_3361_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_3354_, v_declHint_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3353_, v_a_3362_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_ref_3364_, lean_object* v_msg_3365_, lean_object* v_declHint_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3364_, v_msg_3365_, v_declHint_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v_ref_3364_);
return v_res_3372_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0));
v___x_3375_ = l_Lean_stringToMessageData(v___x_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_3376_, lean_object* v_constName_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; uint8_t v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3383_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_3384_ = 0;
lean_inc(v_constName_3377_);
v___x_3385_ = l_Lean_MessageData_ofConstName(v_constName_3377_, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3383_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_3388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3376_, v___x_3388_, v_constName_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_3390_, lean_object* v_constName_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3390_, v_constName_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v_ref_3390_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(lean_object* v_constName_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_ref_3404_; lean_object* v___x_3405_; 
v_ref_3404_ = lean_ctor_get(v___y_3401_, 2);
v___x_3405_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3404_, v_constName_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg___boxed(lean_object* v_constName_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(lean_object* v_constName_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; lean_object* v_env_3420_; uint8_t v___x_3421_; lean_object* v___x_3422_; 
v___x_3419_ = lean_st_ref_get(v___y_3417_);
v_env_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc_ref(v_env_3420_);
lean_dec(v___x_3419_);
v___x_3421_ = 0;
lean_inc(v_constName_3413_);
v___x_3422_ = l_Lean_Environment_find_x3f(v_env_3420_, v_constName_3413_, v___x_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3423_;
}
else
{
lean_object* v_val_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec(v_constName_3413_);
v_val_3424_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3422_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_val_3424_);
lean_dec(v___x_3422_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set_tag(v___x_3426_, 0);
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_val_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3___boxed(lean_object* v_constName_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(v_constName_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator(lean_object* v_elimName_3439_, uint8_t v_induction_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_box(0);
lean_inc(v_elimName_3439_);
v___x_3447_ = l_Lean_Meta_getElimInfo(v_elimName_3439_, v___x_3446_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3449_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref_known(v___x_3447_, 1);
lean_inc(v_elimName_3439_);
v___x_3449_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(v_elimName_3439_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3451_; lean_object* v___f_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; lean_object* v___x_3455_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref_known(v___x_3449_, 1);
v___x_3451_ = lean_box(v_induction_3440_);
v___f_3452_ = lean_alloc_closure((void*)(l_Lean_Meta_mkCustomEliminator___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3452_, 0, v_a_3448_);
lean_closure_set(v___f_3452_, 1, v___x_3451_);
lean_closure_set(v___f_3452_, 2, v_elimName_3439_);
v___x_3453_ = l_Lean_ConstantInfo_type(v_a_3450_);
lean_dec(v_a_3450_);
v___x_3454_ = 0;
v___x_3455_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v___x_3453_, v___f_3452_, v___x_3454_, v___x_3454_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3455_;
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec(v_a_3448_);
lean_dec(v_elimName_3439_);
v_a_3456_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3449_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3449_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v_elimName_3439_);
v_a_3464_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3447_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3447_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___boxed(lean_object* v_elimName_3472_, lean_object* v_induction_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
uint8_t v_induction_boxed_3479_; lean_object* v_res_3480_; 
v_induction_boxed_3479_ = lean_unbox(v_induction_3473_);
v_res_3480_ = l_Lean_Meta_mkCustomEliminator(v_elimName_3472_, v_induction_boxed_3479_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(lean_object* v_upperBound_3481_, lean_object* v___x_3482_, lean_object* v_xs_3483_, lean_object* v___x_3484_, lean_object* v_inst_3485_, lean_object* v_R_3486_, lean_object* v_a_3487_, lean_object* v_b_3488_, lean_object* v_c_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v_upperBound_3481_, v___x_3482_, v_xs_3483_, v___x_3484_, v_a_3487_, v_b_3488_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___boxed(lean_object* v_upperBound_3496_, lean_object* v___x_3497_, lean_object* v_xs_3498_, lean_object* v___x_3499_, lean_object* v_inst_3500_, lean_object* v_R_3501_, lean_object* v_a_3502_, lean_object* v_b_3503_, lean_object* v_c_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(v_upperBound_3496_, v___x_3497_, v_xs_3498_, v___x_3499_, v_inst_3500_, v_R_3501_, v_a_3502_, v_b_3503_, v_c_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec_ref(v___x_3499_);
lean_dec_ref(v_xs_3498_);
lean_dec_ref(v___x_3497_);
lean_dec(v_upperBound_3496_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(lean_object* v_upperBound_3511_, lean_object* v___x_3512_, lean_object* v___x_3513_, lean_object* v_xs_3514_, lean_object* v_inst_3515_, lean_object* v_R_3516_, lean_object* v_a_3517_, lean_object* v_b_3518_, lean_object* v_c_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v_upperBound_3511_, v___x_3512_, v___x_3513_, v_xs_3514_, v_a_3517_, v_b_3518_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___boxed(lean_object* v_upperBound_3526_, lean_object* v___x_3527_, lean_object* v___x_3528_, lean_object* v_xs_3529_, lean_object* v_inst_3530_, lean_object* v_R_3531_, lean_object* v_a_3532_, lean_object* v_b_3533_, lean_object* v_c_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(v_upperBound_3526_, v___x_3527_, v___x_3528_, v_xs_3529_, v_inst_3530_, v_R_3531_, v_a_3532_, v_b_3533_, v_c_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v_xs_3529_);
lean_dec_ref(v___x_3528_);
lean_dec(v___x_3527_);
lean_dec(v_upperBound_3526_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(lean_object* v_00_u03b1_3541_, lean_object* v_constName_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___boxed(lean_object* v_00_u03b1_3549_, lean_object* v_constName_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(v_00_u03b1_3549_, v_constName_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_3557_, lean_object* v_ref_3558_, lean_object* v_constName_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3558_, v_constName_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3566_, lean_object* v_ref_3567_, lean_object* v_constName_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(v_00_u03b1_3566_, v_ref_3567_, v_constName_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v_ref_3567_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3575_, lean_object* v_ref_3576_, lean_object* v_msg_3577_, lean_object* v_declHint_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3576_, v_msg_3577_, v_declHint_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3585_, lean_object* v_ref_3586_, lean_object* v_msg_3587_, lean_object* v_declHint_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3585_, v_ref_3586_, v_msg_3587_, v_declHint_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v_ref_3586_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(lean_object* v_msg_3595_, lean_object* v_declHint_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3595_, v_declHint_3596_, v___y_3600_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_3603_, lean_object* v_declHint_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(v_msg_3603_, v_declHint_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(lean_object* v_00_u03b1_3611_, lean_object* v_ref_3612_, lean_object* v_msg_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3612_, v_msg_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3620_, lean_object* v_ref_3621_, lean_object* v_msg_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(v_00_u03b1_3620_, v_ref_3621_, v_msg_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v_ref_3621_);
return v_res_3628_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3629_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0);
v___x_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
return v___x_3631_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
v___x_3633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
return v___x_3633_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
v___x_3635_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
lean_ctor_set(v___x_3635_, 2, v___x_3634_);
lean_ctor_set(v___x_3635_, 3, v___x_3634_);
lean_ctor_set(v___x_3635_, 4, v___x_3634_);
lean_ctor_set(v___x_3635_, 5, v___x_3634_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(lean_object* v_ext_3636_, lean_object* v_b_3637_, uint8_t v_kind_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v_toCold_3643_; lean_object* v_currNamespace_3644_; lean_object* v___x_3645_; lean_object* v_env_3646_; lean_object* v_nextMacroScope_3647_; lean_object* v_ngen_3648_; lean_object* v_auxDeclNGen_3649_; lean_object* v_traceState_3650_; lean_object* v_messages_3651_; lean_object* v_infoState_3652_; lean_object* v_snapshotTasks_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3680_; 
v_toCold_3643_ = lean_ctor_get(v___y_3640_, 0);
v_currNamespace_3644_ = lean_ctor_get(v_toCold_3643_, 4);
v___x_3645_ = lean_st_ref_take(v___y_3641_);
v_env_3646_ = lean_ctor_get(v___x_3645_, 0);
v_nextMacroScope_3647_ = lean_ctor_get(v___x_3645_, 1);
v_ngen_3648_ = lean_ctor_get(v___x_3645_, 2);
v_auxDeclNGen_3649_ = lean_ctor_get(v___x_3645_, 3);
v_traceState_3650_ = lean_ctor_get(v___x_3645_, 4);
v_messages_3651_ = lean_ctor_get(v___x_3645_, 6);
v_infoState_3652_ = lean_ctor_get(v___x_3645_, 7);
v_snapshotTasks_3653_ = lean_ctor_get(v___x_3645_, 8);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3680_ == 0)
{
lean_object* v_unused_3681_; 
v_unused_3681_ = lean_ctor_get(v___x_3645_, 5);
lean_dec(v_unused_3681_);
v___x_3655_ = v___x_3645_;
v_isShared_3656_ = v_isSharedCheck_3680_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_snapshotTasks_3653_);
lean_inc(v_infoState_3652_);
lean_inc(v_messages_3651_);
lean_inc(v_traceState_3650_);
lean_inc(v_auxDeclNGen_3649_);
lean_inc(v_ngen_3648_);
lean_inc(v_nextMacroScope_3647_);
lean_inc(v_env_3646_);
lean_dec(v___x_3645_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3680_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
lean_inc(v_currNamespace_3644_);
v___x_3657_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3646_, v_ext_3636_, v_b_3637_, v_kind_3638_, v_currNamespace_3644_);
v___x_3658_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 5, v___x_3658_);
lean_ctor_set(v___x_3655_, 0, v___x_3657_);
v___x_3660_ = v___x_3655_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_nextMacroScope_3647_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_ngen_3648_);
lean_ctor_set(v_reuseFailAlloc_3679_, 3, v_auxDeclNGen_3649_);
lean_ctor_set(v_reuseFailAlloc_3679_, 4, v_traceState_3650_);
lean_ctor_set(v_reuseFailAlloc_3679_, 5, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3679_, 6, v_messages_3651_);
lean_ctor_set(v_reuseFailAlloc_3679_, 7, v_infoState_3652_);
lean_ctor_set(v_reuseFailAlloc_3679_, 8, v_snapshotTasks_3653_);
v___x_3660_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v_mctx_3663_; lean_object* v_zetaDeltaFVarIds_3664_; lean_object* v_postponed_3665_; lean_object* v_diag_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3677_; 
v___x_3661_ = lean_st_ref_put(v___y_3641_, v___x_3660_);
v___x_3662_ = lean_st_ref_take(v___y_3639_);
v_mctx_3663_ = lean_ctor_get(v___x_3662_, 0);
v_zetaDeltaFVarIds_3664_ = lean_ctor_get(v___x_3662_, 2);
v_postponed_3665_ = lean_ctor_get(v___x_3662_, 3);
v_diag_3666_ = lean_ctor_get(v___x_3662_, 4);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v___x_3662_, 1);
lean_dec(v_unused_3678_);
v___x_3668_ = v___x_3662_;
v_isShared_3669_ = v_isSharedCheck_3677_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_diag_3666_);
lean_inc(v_postponed_3665_);
lean_inc(v_zetaDeltaFVarIds_3664_);
lean_inc(v_mctx_3663_);
lean_dec(v___x_3662_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3677_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3670_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 1, v___x_3670_);
v___x_3672_ = v___x_3668_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_mctx_3663_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_zetaDeltaFVarIds_3664_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_postponed_3665_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_diag_3666_);
v___x_3672_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3673_ = lean_st_ref_put(v___y_3639_, v___x_3672_);
v___x_3674_ = lean_box(0);
v___x_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
return v___x_3675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___boxed(lean_object* v_ext_3682_, lean_object* v_b_3683_, lean_object* v_kind_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
uint8_t v_kind_boxed_3689_; lean_object* v_res_3690_; 
v_kind_boxed_3689_ = lean_unbox(v_kind_3684_);
v_res_3690_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v_ext_3682_, v_b_3683_, v_kind_boxed_3689_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(lean_object* v_00_u03b1_3691_, lean_object* v_00_u03b2_3692_, lean_object* v_00_u03c3_3693_, lean_object* v_ext_3694_, lean_object* v_b_3695_, uint8_t v_kind_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v_ext_3694_, v_b_3695_, v_kind_3696_, v___y_3698_, v___y_3699_, v___y_3700_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___boxed(lean_object* v_00_u03b1_3703_, lean_object* v_00_u03b2_3704_, lean_object* v_00_u03c3_3705_, lean_object* v_ext_3706_, lean_object* v_b_3707_, lean_object* v_kind_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
uint8_t v_kind_boxed_3714_; lean_object* v_res_3715_; 
v_kind_boxed_3714_ = lean_unbox(v_kind_3708_);
v_res_3715_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(v_00_u03b1_3703_, v_00_u03b2_3704_, v_00_u03c3_3705_, v_ext_3706_, v_b_3707_, v_kind_boxed_3714_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator(lean_object* v_declName_3716_, uint8_t v_attrKind_3717_, uint8_t v_induction_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Lean_Meta_mkCustomEliminator(v_declName_3716_, v_induction_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___x_3724_, 1);
v___x_3726_ = l_Lean_Meta_customEliminatorExt;
v___x_3727_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v___x_3726_, v_a_3725_, v_attrKind_3717_, v_a_3720_, v_a_3721_, v_a_3722_);
return v___x_3727_;
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
v_a_3728_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3724_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3724_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator___boxed(lean_object* v_declName_3736_, lean_object* v_attrKind_3737_, lean_object* v_induction_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
uint8_t v_attrKind_boxed_3744_; uint8_t v_induction_boxed_3745_; lean_object* v_res_3746_; 
v_attrKind_boxed_3744_ = lean_unbox(v_attrKind_3737_);
v_induction_boxed_3745_ = lean_unbox(v_induction_3738_);
v_res_3746_ = l_Lean_Meta_addCustomEliminator(v_declName_3736_, v_attrKind_boxed_3744_, v_induction_boxed_3745_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
lean_dec(v_a_3740_);
lean_dec_ref(v_a_3739_);
return v_res_3746_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3753_; uint64_t v___x_3754_; 
v___x_3753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3754_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3753_);
return v___x_3754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3755_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3757_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set_uint64(v___x_3757_, sizeof(void*)*1, v___x_3755_);
return v___x_3757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3758_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
return v___x_3760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3762_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
lean_ctor_set(v___x_3762_, 2, v___x_3761_);
lean_ctor_set(v___x_3762_, 3, v___x_3761_);
lean_ctor_set(v___x_3762_, 4, v___x_3761_);
lean_ctor_set(v___x_3762_, 5, v___x_3761_);
return v___x_3762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
lean_ctor_set(v___x_3764_, 2, v___x_3763_);
lean_ctor_set(v___x_3764_, 3, v___x_3763_);
lean_ctor_set(v___x_3764_, 4, v___x_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object* v___x_3765_, lean_object* v___x_3766_, lean_object* v_declName_3767_, lean_object* v_x_3768_, uint8_t v_attrKind_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
uint8_t v___x_3773_; uint8_t v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; size_t v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3773_ = 1;
v___x_3774_ = 0;
v___x_3775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3777_ = lean_unsigned_to_nat(32u);
v___x_3778_ = lean_mk_empty_array_with_capacity(v___x_3777_);
v___x_3779_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3780_ = ((size_t)5ULL);
lean_inc_n(v___x_3765_, 6);
v___x_3781_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3781_, 0, v___x_3779_);
lean_ctor_set(v___x_3781_, 1, v___x_3778_);
lean_ctor_set(v___x_3781_, 2, v___x_3765_);
lean_ctor_set(v___x_3781_, 3, v___x_3765_);
lean_ctor_set_usize(v___x_3781_, 4, v___x_3780_);
v___x_3782_ = lean_box(1);
lean_inc_ref(v___x_3781_);
v___x_3783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3776_);
lean_ctor_set(v___x_3783_, 1, v___x_3781_);
lean_ctor_set(v___x_3783_, 2, v___x_3782_);
v___x_3784_ = lean_mk_empty_array_with_capacity(v___x_3765_);
v___x_3785_ = lean_box(0);
lean_inc(v___x_3766_);
v___x_3786_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3786_, 0, v___x_3775_);
lean_ctor_set(v___x_3786_, 1, v___x_3766_);
lean_ctor_set(v___x_3786_, 2, v___x_3783_);
lean_ctor_set(v___x_3786_, 3, v___x_3784_);
lean_ctor_set(v___x_3786_, 4, v___x_3785_);
lean_ctor_set(v___x_3786_, 5, v___x_3765_);
lean_ctor_set(v___x_3786_, 6, v___x_3785_);
lean_ctor_set_uint8(v___x_3786_, sizeof(void*)*7, v___x_3774_);
lean_ctor_set_uint8(v___x_3786_, sizeof(void*)*7 + 1, v___x_3774_);
lean_ctor_set_uint8(v___x_3786_, sizeof(void*)*7 + 2, v___x_3774_);
lean_ctor_set_uint8(v___x_3786_, sizeof(void*)*7 + 3, v___x_3773_);
v___x_3787_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3765_);
lean_ctor_set(v___x_3787_, 1, v___x_3765_);
lean_ctor_set(v___x_3787_, 2, v___x_3765_);
lean_ctor_set(v___x_3787_, 3, v___x_3765_);
lean_ctor_set(v___x_3787_, 4, v___x_3776_);
lean_ctor_set(v___x_3787_, 5, v___x_3776_);
lean_ctor_set(v___x_3787_, 6, v___x_3776_);
lean_ctor_set(v___x_3787_, 7, v___x_3776_);
lean_ctor_set(v___x_3787_, 8, v___x_3776_);
lean_ctor_set(v___x_3787_, 9, v___x_3776_);
lean_ctor_set(v___x_3787_, 10, v___x_3776_);
v___x_3788_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3789_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3787_);
lean_ctor_set(v___x_3790_, 1, v___x_3788_);
lean_ctor_set(v___x_3790_, 2, v___x_3766_);
lean_ctor_set(v___x_3790_, 3, v___x_3781_);
lean_ctor_set(v___x_3790_, 4, v___x_3789_);
v___x_3791_ = lean_st_mk_ref(v___x_3790_);
v___x_3792_ = l_Lean_Meta_addCustomEliminator(v_declName_3767_, v_attrKind_3769_, v___x_3773_, v___x_3786_, v___x_3791_, v___y_3770_, v___y_3771_);
lean_dec_ref_known(v___x_3786_, 7);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3801_; 
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; 
v_unused_3802_ = lean_ctor_get(v___x_3792_, 0);
lean_dec(v_unused_3802_);
v___x_3794_ = v___x_3792_;
v_isShared_3795_ = v_isSharedCheck_3801_;
goto v_resetjp_3793_;
}
else
{
lean_dec(v___x_3792_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3801_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3796_ = lean_st_ref_get(v___x_3791_);
lean_dec(v___x_3791_);
lean_dec(v___x_3796_);
v___x_3797_ = lean_box(0);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 0, v___x_3797_);
v___x_3799_ = v___x_3794_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
else
{
lean_dec(v___x_3791_);
return v___x_3792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v___x_3803_, lean_object* v___x_3804_, lean_object* v_declName_3805_, lean_object* v_x_3806_, lean_object* v_attrKind_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
uint8_t v_attrKind_boxed_3811_; lean_object* v_res_3812_; 
v_attrKind_boxed_3811_ = lean_unbox(v_attrKind_3807_);
v_res_3812_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_3803_, v___x_3804_, v_declName_3805_, v_x_3806_, v_attrKind_boxed_3811_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v_x_3806_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v___x_3817_; lean_object* v_toCold_3818_; lean_object* v_env_3819_; lean_object* v_options_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3817_ = lean_st_ref_get(v___y_3815_);
v_toCold_3818_ = lean_ctor_get(v___y_3814_, 0);
v_env_3819_ = lean_ctor_get(v___x_3817_, 0);
lean_inc_ref(v_env_3819_);
lean_dec(v___x_3817_);
v_options_3820_ = lean_ctor_get(v_toCold_3818_, 2);
v___x_3821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_3822_ = lean_unsigned_to_nat(32u);
v___x_3823_ = lean_mk_empty_array_with_capacity(v___x_3822_);
lean_dec_ref(v___x_3823_);
v___x_3824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
lean_inc_ref(v_options_3820_);
v___x_3825_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3825_, 0, v_env_3819_);
lean_ctor_set(v___x_3825_, 1, v___x_3821_);
lean_ctor_set(v___x_3825_, 2, v___x_3824_);
lean_ctor_set(v___x_3825_, 3, v_options_3820_);
v___x_3826_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
lean_ctor_set(v___x_3826_, 1, v_msgData_3813_);
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3828_, v___y_3829_, v___y_3830_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_ref_3837_; lean_object* v___x_3838_; lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3847_; 
v_ref_3837_ = lean_ctor_get(v___y_3834_, 2);
v___x_3838_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msg_3833_, v___y_3834_, v___y_3835_);
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3841_ = v___x_3838_;
v_isShared_3842_ = v_isSharedCheck_3847_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3838_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3847_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
lean_inc(v_ref_3837_);
v___x_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3843_, 0, v_ref_3837_);
lean_ctor_set(v___x_3843_, 1, v_a_3839_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set_tag(v___x_3841_, 1);
lean_ctor_set(v___x_3841_, 0, v___x_3843_);
v___x_3845_ = v___x_3841_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
return v_res_3852_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3855_ = l_Lean_stringToMessageData(v___x_3854_);
return v___x_3855_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3858_ = l_Lean_stringToMessageData(v___x_3857_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object* v___x_3859_, lean_object* v_decl_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3865_ = l_Lean_MessageData_ofName(v___x_3859_);
v___x_3866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3864_);
lean_ctor_set(v___x_3866_, 1, v___x_3865_);
v___x_3867_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3866_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_3868_, v___y_3861_, v___y_3862_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v___x_3870_, lean_object* v_decl_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_3870_, v_decl_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v_decl_3871_);
return v_res_3875_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_unsigned_to_nat(2729305610u);
v___x_3927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3928_ = l_Lean_Name_num___override(v___x_3927_, v___x_3926_);
return v___x_3928_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3932_ = l_Lean_Name_str___override(v___x_3931_, v___x_3930_);
return v___x_3932_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3936_ = l_Lean_Name_str___override(v___x_3935_, v___x_3934_);
return v___x_3936_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3937_ = lean_unsigned_to_nat(2u);
v___x_3938_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3939_ = l_Lean_Name_num___override(v___x_3938_, v___x_3937_);
return v___x_3939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3946_ = 0;
v___x_3947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3950_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
lean_ctor_set(v___x_3950_, 1, v___x_3948_);
lean_ctor_set(v___x_3950_, 2, v___x_3947_);
lean_ctor_set_uint8(v___x_3950_, sizeof(void*)*3, v___x_3946_);
return v___x_3950_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3951_; lean_object* v___f_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___f_3951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___f_3952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
lean_ctor_set(v___x_3954_, 1, v___f_3952_);
lean_ctor_set(v___x_3954_, 2, v___f_3951_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3957_ = l_Lean_registerBuiltinAttribute(v___x_3956_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v_a_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3960_, lean_object* v_msg_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_3961_, v___y_3962_, v___y_3963_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3966_, lean_object* v_msg_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(v_00_u03b1_3966_, v_msg_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3974_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3976_ = l_Lean_addBuiltinDocString(v___x_3974_, v___x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v_a_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object* v___x_3979_, lean_object* v___x_3980_, lean_object* v_declName_3981_, lean_object* v_x_3982_, uint8_t v_attrKind_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
uint8_t v___x_3987_; uint8_t v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; size_t v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_3987_ = 0;
v___x_3988_ = 1;
v___x_3989_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3990_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3991_ = lean_unsigned_to_nat(32u);
v___x_3992_ = lean_mk_empty_array_with_capacity(v___x_3991_);
v___x_3993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3994_ = ((size_t)5ULL);
lean_inc_n(v___x_3979_, 6);
v___x_3995_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3995_, 0, v___x_3993_);
lean_ctor_set(v___x_3995_, 1, v___x_3992_);
lean_ctor_set(v___x_3995_, 2, v___x_3979_);
lean_ctor_set(v___x_3995_, 3, v___x_3979_);
lean_ctor_set_usize(v___x_3995_, 4, v___x_3994_);
v___x_3996_ = lean_box(1);
lean_inc_ref(v___x_3995_);
v___x_3997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3990_);
lean_ctor_set(v___x_3997_, 1, v___x_3995_);
lean_ctor_set(v___x_3997_, 2, v___x_3996_);
v___x_3998_ = lean_mk_empty_array_with_capacity(v___x_3979_);
v___x_3999_ = lean_box(0);
lean_inc(v___x_3980_);
v___x_4000_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4000_, 0, v___x_3989_);
lean_ctor_set(v___x_4000_, 1, v___x_3980_);
lean_ctor_set(v___x_4000_, 2, v___x_3997_);
lean_ctor_set(v___x_4000_, 3, v___x_3998_);
lean_ctor_set(v___x_4000_, 4, v___x_3999_);
lean_ctor_set(v___x_4000_, 5, v___x_3979_);
lean_ctor_set(v___x_4000_, 6, v___x_3999_);
lean_ctor_set_uint8(v___x_4000_, sizeof(void*)*7, v___x_3987_);
lean_ctor_set_uint8(v___x_4000_, sizeof(void*)*7 + 1, v___x_3987_);
lean_ctor_set_uint8(v___x_4000_, sizeof(void*)*7 + 2, v___x_3987_);
lean_ctor_set_uint8(v___x_4000_, sizeof(void*)*7 + 3, v___x_3988_);
v___x_4001_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3979_);
lean_ctor_set(v___x_4001_, 1, v___x_3979_);
lean_ctor_set(v___x_4001_, 2, v___x_3979_);
lean_ctor_set(v___x_4001_, 3, v___x_3979_);
lean_ctor_set(v___x_4001_, 4, v___x_3990_);
lean_ctor_set(v___x_4001_, 5, v___x_3990_);
lean_ctor_set(v___x_4001_, 6, v___x_3990_);
lean_ctor_set(v___x_4001_, 7, v___x_3990_);
lean_ctor_set(v___x_4001_, 8, v___x_3990_);
lean_ctor_set(v___x_4001_, 9, v___x_3990_);
lean_ctor_set(v___x_4001_, 10, v___x_3990_);
v___x_4002_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4003_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4001_);
lean_ctor_set(v___x_4004_, 1, v___x_4002_);
lean_ctor_set(v___x_4004_, 2, v___x_3980_);
lean_ctor_set(v___x_4004_, 3, v___x_3995_);
lean_ctor_set(v___x_4004_, 4, v___x_4003_);
v___x_4005_ = lean_st_mk_ref(v___x_4004_);
v___x_4006_ = l_Lean_Meta_addCustomEliminator(v_declName_3981_, v_attrKind_3983_, v___x_3987_, v___x_4000_, v___x_4005_, v___y_3984_, v___y_3985_);
lean_dec_ref_known(v___x_4000_, 7);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4015_; 
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4015_ == 0)
{
lean_object* v_unused_4016_; 
v_unused_4016_ = lean_ctor_get(v___x_4006_, 0);
lean_dec(v_unused_4016_);
v___x_4008_ = v___x_4006_;
v_isShared_4009_ = v_isSharedCheck_4015_;
goto v_resetjp_4007_;
}
else
{
lean_dec(v___x_4006_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4015_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4013_; 
v___x_4010_ = lean_st_ref_get(v___x_4005_);
lean_dec(v___x_4005_);
lean_dec(v___x_4010_);
v___x_4011_ = lean_box(0);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v___x_4011_);
v___x_4013_ = v___x_4008_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
else
{
lean_dec(v___x_4005_);
return v___x_4006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v___x_4017_, lean_object* v___x_4018_, lean_object* v_declName_4019_, lean_object* v_x_4020_, lean_object* v_attrKind_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
uint8_t v_attrKind_boxed_4025_; lean_object* v_res_4026_; 
v_attrKind_boxed_4025_ = lean_unbox(v_attrKind_4021_);
v_res_4026_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_4017_, v___x_4018_, v_declName_4019_, v_x_4020_, v_attrKind_boxed_4025_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v_x_4020_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object* v___x_4027_, lean_object* v_decl_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4033_ = l_Lean_MessageData_ofName(v___x_4027_);
v___x_4034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4032_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
v___x_4035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4034_);
lean_ctor_set(v___x_4036_, 1, v___x_4035_);
v___x_4037_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_4036_, v___y_4029_, v___y_4030_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v___x_4038_, lean_object* v_decl_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_4038_, v_decl_4039_, v___y_4040_, v___y_4041_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v_decl_4039_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4076_ = l_Lean_registerBuiltinAttribute(v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v_a_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4083_ = l_Lean_addBuiltinDocString(v___x_4081_, v___x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v_a_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg(lean_object* v_a_4086_){
_start:
{
lean_object* v___x_4088_; lean_object* v_env_4089_; lean_object* v___x_4090_; lean_object* v_ext_4091_; lean_object* v_toEnvExtension_4092_; lean_object* v_asyncMode_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4088_ = lean_st_ref_get(v_a_4086_);
v_env_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc_ref(v_env_4089_);
lean_dec(v___x_4088_);
v___x_4090_ = l_Lean_Meta_customEliminatorExt;
v_ext_4091_ = lean_ctor_get(v___x_4090_, 1);
v_toEnvExtension_4092_ = lean_ctor_get(v_ext_4091_, 0);
v_asyncMode_4093_ = lean_ctor_get(v_toEnvExtension_4092_, 2);
v___x_4094_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
v___x_4095_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4094_, v___x_4090_, v_env_4089_, v_asyncMode_4093_);
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg___boxed(lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_4097_);
lean_dec(v_a_4097_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators(lean_object* v_a_4100_, lean_object* v_a_4101_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_4101_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___boxed(lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Lean_Meta_getCustomEliminators(v_a_4104_, v_a_4105_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_a_4108_, lean_object* v_x_4109_){
_start:
{
if (lean_obj_tag(v_x_4109_) == 0)
{
lean_object* v___x_4110_; 
v___x_4110_ = lean_box(0);
return v___x_4110_;
}
else
{
lean_object* v_key_4111_; lean_object* v_value_4112_; lean_object* v_tail_4113_; lean_object* v_fst_4114_; lean_object* v_snd_4115_; lean_object* v_fst_4116_; lean_object* v_snd_4117_; uint8_t v___x_4126_; 
v_key_4111_ = lean_ctor_get(v_x_4109_, 0);
v_value_4112_ = lean_ctor_get(v_x_4109_, 1);
v_tail_4113_ = lean_ctor_get(v_x_4109_, 2);
v_fst_4114_ = lean_ctor_get(v_key_4111_, 0);
v_snd_4115_ = lean_ctor_get(v_key_4111_, 1);
v_fst_4116_ = lean_ctor_get(v_a_4108_, 0);
v_snd_4117_ = lean_ctor_get(v_a_4108_, 1);
v___x_4126_ = lean_unbox(v_fst_4116_);
if (v___x_4126_ == 0)
{
uint8_t v___x_4127_; 
v___x_4127_ = lean_unbox(v_fst_4114_);
if (v___x_4127_ == 0)
{
goto v___jp_4118_;
}
else
{
v_x_4109_ = v_tail_4113_;
goto _start;
}
}
else
{
uint8_t v___x_4129_; 
v___x_4129_ = lean_unbox(v_fst_4114_);
if (v___x_4129_ == 0)
{
v_x_4109_ = v_tail_4113_;
goto _start;
}
else
{
goto v___jp_4118_;
}
}
v___jp_4118_:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; 
v___x_4119_ = lean_array_get_size(v_snd_4115_);
v___x_4120_ = lean_array_get_size(v_snd_4117_);
v___x_4121_ = lean_nat_dec_eq(v___x_4119_, v___x_4120_);
if (v___x_4121_ == 0)
{
v_x_4109_ = v_tail_4113_;
goto _start;
}
else
{
uint8_t v___x_4123_; 
v___x_4123_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4115_, v_snd_4117_, v___x_4119_);
if (v___x_4123_ == 0)
{
v_x_4109_ = v_tail_4113_;
goto _start;
}
else
{
lean_object* v___x_4125_; 
lean_inc(v_value_4112_);
v___x_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_value_4112_);
return v___x_4125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_4131_, lean_object* v_x_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4131_, v_x_4132_);
lean_dec(v_x_4132_);
lean_dec_ref(v_a_4131_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(lean_object* v_m_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v_buckets_4136_; lean_object* v_fst_4137_; lean_object* v_snd_4138_; lean_object* v___x_4139_; uint64_t v___y_4141_; uint64_t v___y_4142_; uint64_t v___y_4158_; uint8_t v___x_4166_; 
v_buckets_4136_ = lean_ctor_get(v_m_4134_, 1);
v_fst_4137_ = lean_ctor_get(v_a_4135_, 0);
v_snd_4138_ = lean_ctor_get(v_a_4135_, 1);
v___x_4139_ = lean_array_get_size(v_buckets_4136_);
v___x_4166_ = lean_unbox(v_fst_4137_);
if (v___x_4166_ == 0)
{
uint64_t v___x_4167_; 
v___x_4167_ = 13ULL;
v___y_4158_ = v___x_4167_;
goto v___jp_4157_;
}
else
{
uint64_t v___x_4168_; 
v___x_4168_ = 11ULL;
v___y_4158_ = v___x_4168_;
goto v___jp_4157_;
}
v___jp_4140_:
{
uint64_t v___x_4143_; uint64_t v___x_4144_; uint64_t v___x_4145_; uint64_t v_fold_4146_; uint64_t v___x_4147_; uint64_t v___x_4148_; uint64_t v___x_4149_; size_t v___x_4150_; size_t v___x_4151_; size_t v___x_4152_; size_t v___x_4153_; size_t v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4143_ = lean_uint64_mix_hash(v___y_4141_, v___y_4142_);
v___x_4144_ = 32ULL;
v___x_4145_ = lean_uint64_shift_right(v___x_4143_, v___x_4144_);
v_fold_4146_ = lean_uint64_xor(v___x_4143_, v___x_4145_);
v___x_4147_ = 16ULL;
v___x_4148_ = lean_uint64_shift_right(v_fold_4146_, v___x_4147_);
v___x_4149_ = lean_uint64_xor(v_fold_4146_, v___x_4148_);
v___x_4150_ = lean_uint64_to_usize(v___x_4149_);
v___x_4151_ = lean_usize_of_nat(v___x_4139_);
v___x_4152_ = ((size_t)1ULL);
v___x_4153_ = lean_usize_sub(v___x_4151_, v___x_4152_);
v___x_4154_ = lean_usize_land(v___x_4150_, v___x_4153_);
v___x_4155_ = lean_array_uget_borrowed(v_buckets_4136_, v___x_4154_);
v___x_4156_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4135_, v___x_4155_);
return v___x_4156_;
}
v___jp_4157_:
{
uint64_t v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; uint8_t v___x_4162_; 
v___x_4159_ = 7ULL;
v___x_4160_ = lean_unsigned_to_nat(0u);
v___x_4161_ = lean_array_get_size(v_snd_4138_);
v___x_4162_ = lean_nat_dec_lt(v___x_4160_, v___x_4161_);
if (v___x_4162_ == 0)
{
v___y_4141_ = v___y_4158_;
v___y_4142_ = v___x_4159_;
goto v___jp_4140_;
}
else
{
size_t v___x_4163_; size_t v___x_4164_; uint64_t v___x_4165_; 
v___x_4163_ = ((size_t)0ULL);
v___x_4164_ = lean_usize_of_nat(v___x_4161_);
v___x_4165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4138_, v___x_4163_, v___x_4164_, v___x_4159_);
v___y_4141_ = v___y_4158_;
v___y_4142_ = v___x_4165_;
goto v___jp_4140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_m_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_4169_, v_a_4170_);
lean_dec_ref(v_a_4170_);
lean_dec_ref(v_m_4169_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_4172_, lean_object* v_vals_4173_, lean_object* v_i_4174_, lean_object* v_k_4175_){
_start:
{
lean_object* v___x_4180_; uint8_t v___x_4181_; 
v___x_4180_ = lean_array_get_size(v_keys_4172_);
v___x_4181_ = lean_nat_dec_lt(v_i_4174_, v___x_4180_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; 
lean_dec(v_i_4174_);
v___x_4182_ = lean_box(0);
return v___x_4182_;
}
else
{
lean_object* v_fst_4183_; lean_object* v_snd_4184_; lean_object* v_k_x27_4185_; lean_object* v_fst_4186_; lean_object* v_snd_4187_; uint8_t v___y_4189_; uint8_t v___x_4196_; 
v_fst_4183_ = lean_ctor_get(v_k_4175_, 0);
v_snd_4184_ = lean_ctor_get(v_k_4175_, 1);
v_k_x27_4185_ = lean_array_fget_borrowed(v_keys_4172_, v_i_4174_);
v_fst_4186_ = lean_ctor_get(v_k_x27_4185_, 0);
v_snd_4187_ = lean_ctor_get(v_k_x27_4185_, 1);
v___x_4196_ = lean_unbox(v_fst_4186_);
if (v___x_4196_ == 0)
{
uint8_t v___x_4197_; 
v___x_4197_ = lean_unbox(v_fst_4183_);
if (v___x_4197_ == 0)
{
v___y_4189_ = v___x_4181_;
goto v___jp_4188_;
}
else
{
goto v___jp_4176_;
}
}
else
{
uint8_t v___x_4198_; 
v___x_4198_ = lean_unbox(v_fst_4183_);
v___y_4189_ = v___x_4198_;
goto v___jp_4188_;
}
v___jp_4188_:
{
if (v___y_4189_ == 0)
{
goto v___jp_4176_;
}
else
{
lean_object* v___x_4190_; lean_object* v___x_4191_; uint8_t v___x_4192_; 
v___x_4190_ = lean_array_get_size(v_snd_4184_);
v___x_4191_ = lean_array_get_size(v_snd_4187_);
v___x_4192_ = lean_nat_dec_eq(v___x_4190_, v___x_4191_);
if (v___x_4192_ == 0)
{
goto v___jp_4176_;
}
else
{
uint8_t v___x_4193_; 
v___x_4193_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4184_, v_snd_4187_, v___x_4190_);
if (v___x_4193_ == 0)
{
goto v___jp_4176_;
}
else
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4194_ = lean_array_fget_borrowed(v_vals_4173_, v_i_4174_);
lean_dec(v_i_4174_);
lean_inc(v___x_4194_);
v___x_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
return v___x_4195_;
}
}
}
}
}
v___jp_4176_:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = lean_unsigned_to_nat(1u);
v___x_4178_ = lean_nat_add(v_i_4174_, v___x_4177_);
lean_dec(v_i_4174_);
v_i_4174_ = v___x_4178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_4199_, lean_object* v_vals_4200_, lean_object* v_i_4201_, lean_object* v_k_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_4199_, v_vals_4200_, v_i_4201_, v_k_4202_);
lean_dec_ref(v_k_4202_);
lean_dec_ref(v_vals_4200_);
lean_dec_ref(v_keys_4199_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_x_4204_, size_t v_x_4205_, lean_object* v_x_4206_){
_start:
{
if (lean_obj_tag(v_x_4204_) == 0)
{
lean_object* v_es_4207_; lean_object* v___x_4208_; size_t v___x_4209_; size_t v___x_4210_; lean_object* v_j_4211_; lean_object* v___x_4212_; 
v_es_4207_ = lean_ctor_get(v_x_4204_, 0);
v___x_4208_ = lean_box(2);
v___x_4209_ = ((size_t)31ULL);
v___x_4210_ = lean_usize_land(v_x_4205_, v___x_4209_);
v_j_4211_ = lean_usize_to_nat(v___x_4210_);
v___x_4212_ = lean_array_get_borrowed(v___x_4208_, v_es_4207_, v_j_4211_);
lean_dec(v_j_4211_);
switch(lean_obj_tag(v___x_4212_))
{
case 0:
{
lean_object* v_key_4213_; lean_object* v_val_4214_; lean_object* v_fst_4215_; lean_object* v_snd_4216_; lean_object* v_fst_4217_; lean_object* v_snd_4218_; uint8_t v___x_4227_; 
v_key_4213_ = lean_ctor_get(v___x_4212_, 0);
v_val_4214_ = lean_ctor_get(v___x_4212_, 1);
v_fst_4215_ = lean_ctor_get(v_x_4206_, 0);
v_snd_4216_ = lean_ctor_get(v_x_4206_, 1);
v_fst_4217_ = lean_ctor_get(v_key_4213_, 0);
v_snd_4218_ = lean_ctor_get(v_key_4213_, 1);
v___x_4227_ = lean_unbox(v_fst_4217_);
if (v___x_4227_ == 0)
{
uint8_t v___x_4228_; 
v___x_4228_ = lean_unbox(v_fst_4215_);
if (v___x_4228_ == 0)
{
goto v___jp_4219_;
}
else
{
lean_object* v___x_4229_; 
v___x_4229_ = lean_box(0);
return v___x_4229_;
}
}
else
{
uint8_t v___x_4230_; 
v___x_4230_ = lean_unbox(v_fst_4215_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_box(0);
return v___x_4231_;
}
else
{
goto v___jp_4219_;
}
}
v___jp_4219_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; uint8_t v___x_4222_; 
v___x_4220_ = lean_array_get_size(v_snd_4216_);
v___x_4221_ = lean_array_get_size(v_snd_4218_);
v___x_4222_ = lean_nat_dec_eq(v___x_4220_, v___x_4221_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; 
v___x_4223_ = lean_box(0);
return v___x_4223_;
}
else
{
uint8_t v___x_4224_; 
v___x_4224_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4216_, v_snd_4218_, v___x_4220_);
if (v___x_4224_ == 0)
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_box(0);
return v___x_4225_;
}
else
{
lean_object* v___x_4226_; 
lean_inc(v_val_4214_);
v___x_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4226_, 0, v_val_4214_);
return v___x_4226_;
}
}
}
}
case 1:
{
lean_object* v_node_4232_; size_t v___x_4233_; size_t v___x_4234_; 
v_node_4232_ = lean_ctor_get(v___x_4212_, 0);
v___x_4233_ = ((size_t)5ULL);
v___x_4234_ = lean_usize_shift_right(v_x_4205_, v___x_4233_);
v_x_4204_ = v_node_4232_;
v_x_4205_ = v___x_4234_;
goto _start;
}
default: 
{
lean_object* v___x_4236_; 
v___x_4236_ = lean_box(0);
return v___x_4236_;
}
}
}
else
{
lean_object* v_ks_4237_; lean_object* v_vs_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v_ks_4237_ = lean_ctor_get(v_x_4204_, 0);
v_vs_4238_ = lean_ctor_get(v_x_4204_, 1);
v___x_4239_ = lean_unsigned_to_nat(0u);
v___x_4240_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_ks_4237_, v_vs_4238_, v___x_4239_, v_x_4206_);
return v___x_4240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_4241_, lean_object* v_x_4242_, lean_object* v_x_4243_){
_start:
{
size_t v_x_2249__boxed_4244_; lean_object* v_res_4245_; 
v_x_2249__boxed_4244_ = lean_unbox_usize(v_x_4242_);
lean_dec(v_x_4242_);
v_res_4245_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4241_, v_x_2249__boxed_4244_, v_x_4243_);
lean_dec_ref(v_x_4243_);
lean_dec_ref(v_x_4241_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(lean_object* v_x_4246_, lean_object* v_x_4247_){
_start:
{
uint64_t v___y_4249_; uint64_t v___y_4250_; lean_object* v_fst_4254_; lean_object* v_snd_4255_; uint64_t v___y_4257_; uint8_t v___x_4265_; 
v_fst_4254_ = lean_ctor_get(v_x_4247_, 0);
v_snd_4255_ = lean_ctor_get(v_x_4247_, 1);
v___x_4265_ = lean_unbox(v_fst_4254_);
if (v___x_4265_ == 0)
{
uint64_t v___x_4266_; 
v___x_4266_ = 13ULL;
v___y_4257_ = v___x_4266_;
goto v___jp_4256_;
}
else
{
uint64_t v___x_4267_; 
v___x_4267_ = 11ULL;
v___y_4257_ = v___x_4267_;
goto v___jp_4256_;
}
v___jp_4248_:
{
uint64_t v___x_4251_; size_t v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = lean_uint64_mix_hash(v___y_4249_, v___y_4250_);
v___x_4252_ = lean_uint64_to_usize(v___x_4251_);
v___x_4253_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4246_, v___x_4252_, v_x_4247_);
return v___x_4253_;
}
v___jp_4256_:
{
uint64_t v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; 
v___x_4258_ = 7ULL;
v___x_4259_ = lean_unsigned_to_nat(0u);
v___x_4260_ = lean_array_get_size(v_snd_4255_);
v___x_4261_ = lean_nat_dec_lt(v___x_4259_, v___x_4260_);
if (v___x_4261_ == 0)
{
v___y_4249_ = v___y_4257_;
v___y_4250_ = v___x_4258_;
goto v___jp_4248_;
}
else
{
size_t v___x_4262_; size_t v___x_4263_; uint64_t v___x_4264_; 
v___x_4262_ = ((size_t)0ULL);
v___x_4263_ = lean_usize_of_nat(v___x_4260_);
v___x_4264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4255_, v___x_4262_, v___x_4263_, v___x_4258_);
v___y_4249_ = v___y_4257_;
v___y_4250_ = v___x_4264_;
goto v___jp_4248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_4268_, lean_object* v_x_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_4268_, v_x_4269_);
lean_dec_ref(v_x_4269_);
lean_dec_ref(v_x_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(lean_object* v_x_4271_, lean_object* v_x_4272_){
_start:
{
uint8_t v_stage_u2081_4273_; 
v_stage_u2081_4273_ = lean_ctor_get_uint8(v_x_4271_, sizeof(void*)*2);
if (v_stage_u2081_4273_ == 0)
{
lean_object* v_map_u2081_4274_; lean_object* v_map_u2082_4275_; lean_object* v___x_4276_; 
v_map_u2081_4274_ = lean_ctor_get(v_x_4271_, 0);
v_map_u2082_4275_ = lean_ctor_get(v_x_4271_, 1);
v___x_4276_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_map_u2082_4275_, v_x_4272_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v___x_4277_; 
v___x_4277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_4274_, v_x_4272_);
return v___x_4277_;
}
else
{
return v___x_4276_;
}
}
else
{
lean_object* v_map_u2081_4278_; lean_object* v___x_4279_; 
v_map_u2081_4278_ = lean_ctor_get(v_x_4271_, 0);
v___x_4279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_4278_, v_x_4272_);
return v___x_4279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg___boxed(lean_object* v_x_4280_, lean_object* v_x_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v_x_4280_, v_x_4281_);
lean_dec_ref(v_x_4281_);
lean_dec_ref(v_x_4280_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(lean_object* v_as_4285_, size_t v_sz_4286_, size_t v_i_4287_, lean_object* v_b_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
uint8_t v___x_4294_; 
v___x_4294_ = lean_usize_dec_lt(v_i_4287_, v_sz_4286_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4295_; 
v___x_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4295_, 0, v_b_4288_);
return v___x_4295_;
}
else
{
lean_object* v_a_4296_; lean_object* v___x_4297_; 
v_a_4296_ = lean_array_uget_borrowed(v_as_4285_, v_i_4287_);
lean_inc(v___y_4292_);
lean_inc_ref(v___y_4291_);
lean_inc(v___y_4290_);
lean_inc_ref(v___y_4289_);
lean_inc(v_a_4296_);
v___x_4297_ = lean_infer_type(v_a_4296_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4299_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v___x_4299_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_a_4298_, v___y_4290_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4328_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4328_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4328_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v_snd_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4326_; 
v_snd_4304_ = lean_ctor_get(v_b_4288_, 1);
v_isSharedCheck_4326_ = !lean_is_exclusive(v_b_4288_);
if (v_isSharedCheck_4326_ == 0)
{
lean_object* v_unused_4327_; 
v_unused_4327_ = lean_ctor_get(v_b_4288_, 0);
lean_dec(v_unused_4327_);
v___x_4306_ = v_b_4288_;
v_isShared_4307_ = v_isSharedCheck_4326_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_snd_4304_);
lean_dec(v_b_4288_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4326_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = l_Lean_Expr_headBeta(v_a_4300_);
v___x_4309_ = l_Lean_Expr_getAppFn(v___x_4308_);
lean_dec_ref(v___x_4308_);
if (lean_obj_tag(v___x_4309_) == 4)
{
lean_object* v_declName_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4314_; 
lean_del_object(v___x_4302_);
v_declName_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_declName_4310_);
lean_dec_ref_known(v___x_4309_, 2);
v___x_4311_ = lean_box(0);
v___x_4312_ = lean_array_push(v_snd_4304_, v_declName_4310_);
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 1, v___x_4312_);
lean_ctor_set(v___x_4306_, 0, v___x_4311_);
v___x_4314_ = v___x_4306_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4311_);
lean_ctor_set(v_reuseFailAlloc_4318_, 1, v___x_4312_);
v___x_4314_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
size_t v___x_4315_; size_t v___x_4316_; 
v___x_4315_ = ((size_t)1ULL);
v___x_4316_ = lean_usize_add(v_i_4287_, v___x_4315_);
v_i_4287_ = v___x_4316_;
v_b_4288_ = v___x_4314_;
goto _start;
}
}
else
{
lean_object* v___x_4319_; lean_object* v___x_4321_; 
lean_dec_ref(v___x_4309_);
v___x_4319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0));
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 0, v___x_4319_);
v___x_4321_ = v___x_4306_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4319_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v_snd_4304_);
v___x_4321_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
lean_object* v___x_4323_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v___x_4321_);
v___x_4323_ = v___x_4302_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
}
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
lean_dec_ref(v_b_4288_);
v_a_4329_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4299_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4299_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec_ref(v_b_4288_);
v_a_4337_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4297_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4297_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___boxed(lean_object* v_as_4345_, lean_object* v_sz_4346_, lean_object* v_i_4347_, lean_object* v_b_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
size_t v_sz_boxed_4354_; size_t v_i_boxed_4355_; lean_object* v_res_4356_; 
v_sz_boxed_4354_ = lean_unbox_usize(v_sz_4346_);
lean_dec(v_sz_4346_);
v_i_boxed_4355_ = lean_unbox_usize(v_i_4347_);
lean_dec(v_i_4347_);
v_res_4356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_as_4345_, v_sz_boxed_4354_, v_i_boxed_4355_, v_b_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec_ref(v_as_4345_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f(lean_object* v_targets_4360_, uint8_t v_induction_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
lean_object* v___x_4367_; size_t v_sz_4368_; size_t v___x_4369_; lean_object* v___x_4370_; 
v___x_4367_ = ((lean_object*)(l_Lean_Meta_getCustomEliminator_x3f___closed__0));
v_sz_4368_ = lean_array_size(v_targets_4360_);
v___x_4369_ = ((size_t)0ULL);
v___x_4370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_targets_4360_, v_sz_4368_, v___x_4369_, v___x_4367_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4402_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4373_ = v___x_4370_;
v_isShared_4374_ = v_isSharedCheck_4402_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4370_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4402_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v_fst_4375_; 
v_fst_4375_ = lean_ctor_get(v_a_4371_, 0);
if (lean_obj_tag(v_fst_4375_) == 0)
{
lean_object* v_snd_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4396_; 
v_snd_4376_ = lean_ctor_get(v_a_4371_, 1);
v_isSharedCheck_4396_ = !lean_is_exclusive(v_a_4371_);
if (v_isSharedCheck_4396_ == 0)
{
lean_object* v_unused_4397_; 
v_unused_4397_ = lean_ctor_get(v_a_4371_, 0);
lean_dec(v_unused_4397_);
v___x_4378_ = v_a_4371_;
v_isShared_4379_ = v_isSharedCheck_4396_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_snd_4376_);
lean_dec(v_a_4371_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4396_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; lean_object* v_env_4381_; lean_object* v___x_4382_; lean_object* v_ext_4383_; lean_object* v_toEnvExtension_4384_; lean_object* v_asyncMode_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4390_; 
v___x_4380_ = lean_st_ref_get(v_a_4365_);
v_env_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc_ref(v_env_4381_);
lean_dec(v___x_4380_);
v___x_4382_ = l_Lean_Meta_customEliminatorExt;
v_ext_4383_ = lean_ctor_get(v___x_4382_, 1);
v_toEnvExtension_4384_ = lean_ctor_get(v_ext_4383_, 0);
v_asyncMode_4385_ = lean_ctor_get(v_toEnvExtension_4384_, 2);
v___x_4386_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
v___x_4387_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4386_, v___x_4382_, v_env_4381_, v_asyncMode_4385_);
v___x_4388_ = lean_box(v_induction_4361_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4388_);
v___x_4390_ = v___x_4378_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4395_, 1, v_snd_4376_);
v___x_4390_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4393_; 
v___x_4391_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v___x_4387_, v___x_4390_);
lean_dec_ref(v___x_4390_);
lean_dec(v___x_4387_);
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 0, v___x_4391_);
v___x_4393_ = v___x_4373_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
else
{
lean_object* v_val_4398_; lean_object* v___x_4400_; 
lean_inc_ref(v_fst_4375_);
lean_dec(v_a_4371_);
v_val_4398_ = lean_ctor_get(v_fst_4375_, 0);
lean_inc(v_val_4398_);
lean_dec_ref_known(v_fst_4375_, 1);
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 0, v_val_4398_);
v___x_4400_ = v___x_4373_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_val_4398_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
v_a_4403_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4370_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4370_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f___boxed(lean_object* v_targets_4411_, lean_object* v_induction_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
uint8_t v_induction_boxed_4418_; lean_object* v_res_4419_; 
v_induction_boxed_4418_ = lean_unbox(v_induction_4412_);
v_res_4419_ = l_Lean_Meta_getCustomEliminator_x3f(v_targets_4411_, v_induction_boxed_4418_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
lean_dec(v_a_4416_);
lean_dec_ref(v_a_4415_);
lean_dec(v_a_4414_);
lean_dec_ref(v_a_4413_);
lean_dec_ref(v_targets_4411_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(lean_object* v_00_u03b2_4420_, lean_object* v_x_4421_, lean_object* v_x_4422_){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v_x_4421_, v_x_4422_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___boxed(lean_object* v_00_u03b2_4424_, lean_object* v_x_4425_, lean_object* v_x_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(v_00_u03b2_4424_, v_x_4425_, v_x_4426_);
lean_dec_ref(v_x_4426_);
lean_dec_ref(v_x_4425_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(lean_object* v_00_u03b2_4428_, lean_object* v_x_4429_, lean_object* v_x_4430_){
_start:
{
lean_object* v___x_4431_; 
v___x_4431_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_4429_, v_x_4430_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4432_, lean_object* v_x_4433_, lean_object* v_x_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(v_00_u03b2_4432_, v_x_4433_, v_x_4434_);
lean_dec_ref(v_x_4434_);
lean_dec_ref(v_x_4433_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(lean_object* v_00_u03b2_4436_, lean_object* v_m_4437_, lean_object* v_a_4438_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_4437_, v_a_4438_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4440_, lean_object* v_m_4441_, lean_object* v_a_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(v_00_u03b2_4440_, v_m_4441_, v_a_4442_);
lean_dec_ref(v_a_4442_);
lean_dec_ref(v_m_4441_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_4444_, lean_object* v_x_4445_, size_t v_x_4446_, lean_object* v_x_4447_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4445_, v_x_4446_, v_x_4447_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4449_, lean_object* v_x_4450_, lean_object* v_x_4451_, lean_object* v_x_4452_){
_start:
{
size_t v_x_2613__boxed_4453_; lean_object* v_res_4454_; 
v_x_2613__boxed_4453_ = lean_unbox_usize(v_x_4451_);
lean_dec(v_x_4451_);
v_res_4454_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(v_00_u03b2_4449_, v_x_4450_, v_x_2613__boxed_4453_, v_x_4452_);
lean_dec_ref(v_x_4452_);
lean_dec_ref(v_x_4450_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4455_, lean_object* v_a_4456_, lean_object* v_x_4457_){
_start:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4456_, v_x_4457_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4459_, lean_object* v_a_4460_, lean_object* v_x_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(v_00_u03b2_4459_, v_a_4460_, v_x_4461_);
lean_dec(v_x_4461_);
lean_dec_ref(v_a_4460_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4463_, lean_object* v_keys_4464_, lean_object* v_vals_4465_, lean_object* v_heq_4466_, lean_object* v_i_4467_, lean_object* v_k_4468_){
_start:
{
lean_object* v___x_4469_; 
v___x_4469_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_4464_, v_vals_4465_, v_i_4467_, v_k_4468_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4470_, lean_object* v_keys_4471_, lean_object* v_vals_4472_, lean_object* v_heq_4473_, lean_object* v_i_4474_, lean_object* v_k_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(v_00_u03b2_4470_, v_keys_4471_, v_vals_4472_, v_heq_4473_, v_i_4474_, v_k_4475_);
lean_dec_ref(v_k_4475_);
lean_dec_ref(v_vals_4472_);
lean_dec_ref(v_keys_4471_);
return v_res_4476_;
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
