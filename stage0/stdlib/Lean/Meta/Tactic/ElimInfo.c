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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
lean_object* l_Array_takeWhile___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
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
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__0 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__0_value;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "induction"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__1 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__1_value;
static const lean_ctor_object l_Lean_Meta_getElimExprInfo___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Meta_getElimExprInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 113, 55, 104, 212, 17, 5, 40)}};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__2 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__2_value;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eliminator"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__3 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__3_value;
static lean_once_cell_t l_Lean_Meta_getElimExprInfo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getElimExprInfo___closed__4;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nhas type"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__5 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__5_value;
static lean_once_cell_t l_Lean_Meta_getElimExprInfo___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getElimExprInfo___closed__6;
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_switch___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "customEliminatorExt"};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 136, 153, 60, 178, 181, 251, 152)}};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addCustomEliminatorEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 37, 80, 174, 60, 227, 242, 141)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 131, 121, 207, 209, 142, 148, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 30, 84, 209, 139, 131, 70, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 186, 117, 126, 128, 87, 152, 94)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 106, 250, 33, 19, 38, 14, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 152, 58, 59, 147, 212, 205, 253)}};
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
lean_dec_ref(v_x_7_);
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
lean_dec_ref(v_x_164_);
v___x_169_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(v_head_168_);
return v___x_169_;
}
else
{
lean_object* v_head_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_inc(v_tail_167_);
v_head_170_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_head_170_);
lean_dec_ref(v_x_164_);
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
lean_dec_ref(v_x_234_);
v___x_239_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_238_);
return v___x_239_;
}
else
{
lean_object* v_head_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc(v_tail_237_);
v_head_240_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_head_240_);
lean_dec_ref(v_x_234_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg(lean_object* v_cls_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_options_491_; uint8_t v_hasTrace_492_; 
v_options_491_ = lean_ctor_get(v___y_489_, 2);
v_hasTrace_492_ = lean_ctor_get_uint8(v_options_491_, sizeof(void*)*1);
if (v_hasTrace_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v_cls_488_);
v___x_493_ = lean_box(v_hasTrace_492_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
else
{
lean_object* v_inheritedTraceOptions_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_inheritedTraceOptions_495_ = lean_ctor_get(v___y_489_, 13);
v___x_496_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg___closed__1));
v___x_497_ = l_Lean_Name_append(v___x_496_, v_cls_488_);
v___x_498_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_495_, v_options_491_, v___x_497_);
lean_dec(v___x_497_);
v___x_499_ = lean_box(v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg___boxed(lean_object* v_cls_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg(v_cls_501_, v___y_502_);
lean_dec_ref(v___y_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7(lean_object* v_cls_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg(v_cls_505_, v___y_508_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___boxed(lean_object* v_cls_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7(v_cls_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(lean_object* v_msgData_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; lean_object* v_env_526_; lean_object* v___x_527_; lean_object* v_mctx_528_; lean_object* v_lctx_529_; lean_object* v_options_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_525_ = lean_st_ref_get(v___y_523_);
v_env_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_env_526_);
lean_dec(v___x_525_);
v___x_527_ = lean_st_ref_get(v___y_521_);
v_mctx_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_mctx_528_);
lean_dec(v___x_527_);
v_lctx_529_ = lean_ctor_get(v___y_520_, 2);
v_options_530_ = lean_ctor_get(v___y_522_, 2);
lean_inc_ref(v_options_530_);
lean_inc_ref(v_lctx_529_);
v___x_531_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_531_, 0, v_env_526_);
lean_ctor_set(v___x_531_, 1, v_mctx_528_);
lean_ctor_set(v___x_531_, 2, v_lctx_529_);
lean_ctor_set(v___x_531_, 3, v_options_530_);
v___x_532_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v_msgData_519_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2___boxed(lean_object* v_msgData_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msgData_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(lean_object* v_msg_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_ref_547_; lean_object* v___x_548_; lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_557_; 
v_ref_547_ = lean_ctor_get(v___y_544_, 5);
v___x_548_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_557_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
lean_inc(v_ref_547_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v_ref_547_);
lean_ctor_set(v___x_553_, 1, v_a_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 1);
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg___boxed(lean_object* v_msg_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
return v_res_564_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6));
v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(lean_object* v_a_577_, lean_object* v_x_578_, lean_object* v_motiveParams_579_, lean_object* v_motiveResultType_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = lean_array_get_size(v_motiveParams_579_);
v___x_595_ = lean_array_get_size(v_x_578_);
v___x_596_ = lean_nat_dec_eq(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_597_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3);
v___x_598_ = l_Nat_reprFast(v___x_595_);
v___x_599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___x_600_ = l_Lean_MessageData_ofFormat(v___x_599_);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_597_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = l_Nat_reprFast(v___x_594_);
v___x_605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___x_606_ = l_Lean_MessageData_ofFormat(v___x_605_);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_603_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = l_Lean_indentExpr(v_a_577_);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_611_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_612_;
}
else
{
goto v___jp_586_;
}
v___jp_586_:
{
uint8_t v___x_587_; 
v___x_587_ = l_Lean_Expr_isSort(v_motiveResultType_580_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1);
v___x_589_ = l_Lean_indentExpr(v_a_577_);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_590_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec_ref(v_a_577_);
v___x_592_ = lean_box(0);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed(lean_object* v_a_613_, lean_object* v_x_614_, lean_object* v_motiveParams_615_, lean_object* v_motiveResultType_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(v_a_613_, v_x_614_, v_motiveParams_615_, v_motiveResultType_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec_ref(v_motiveResultType_616_);
lean_dec_ref(v_motiveParams_615_);
lean_dec_ref(v_x_614_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__3(lean_object* v_xs_623_, lean_object* v_v_624_, lean_object* v_i_625_){
_start:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_array_get_size(v_xs_623_);
v___x_627_ = lean_nat_dec_lt(v_i_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec(v_i_625_);
v___x_628_ = lean_box(0);
return v___x_628_;
}
else
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_array_fget_borrowed(v_xs_623_, v_i_625_);
v___x_630_ = lean_expr_eqv(v___x_629_, v_v_624_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v_i_625_, v___x_631_);
lean_dec(v_i_625_);
v_i_625_ = v___x_632_;
goto _start;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v_i_625_);
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__3___boxed(lean_object* v_xs_635_, lean_object* v_v_636_, lean_object* v_i_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__3(v_xs_635_, v_v_636_, v_i_637_);
lean_dec_ref(v_v_636_);
lean_dec_ref(v_xs_635_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(lean_object* v_xs_639_, lean_object* v_v_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__3(v_xs_639_, v_v_640_, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0___boxed(lean_object* v_xs_643_, lean_object* v_v_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(v_xs_643_, v_v_644_);
lean_dec_ref(v_v_644_);
lean_dec_ref(v_xs_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(lean_object* v_xs_646_, lean_object* v_v_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(v_xs_646_, v_v_647_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_box(0);
return v___x_649_;
}
else
{
lean_object* v_val_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
v_val_650_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_648_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_val_650_);
lean_dec(v___x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_val_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0___boxed(lean_object* v_xs_658_, lean_object* v_v_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_658_, v_v_659_);
lean_dec_ref(v_v_659_);
lean_dec_ref(v_xs_658_);
return v_res_660_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(lean_object* v_xs_664_, lean_object* v_a_665_, size_t v_sz_666_, size_t v_i_667_, lean_object* v_bs_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
uint8_t v___x_674_; 
v___x_674_ = lean_usize_dec_lt(v_i_667_, v_sz_666_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_dec_ref(v_a_665_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v_bs_668_);
return v___x_675_;
}
else
{
lean_object* v_v_676_; lean_object* v___x_677_; lean_object* v_bs_x27_678_; lean_object* v_a_680_; lean_object* v___x_685_; 
v_v_676_ = lean_array_uget(v_bs_668_, v_i_667_);
v___x_677_ = lean_unsigned_to_nat(0u);
v_bs_x27_678_ = lean_array_uset(v_bs_668_, v_i_667_, v___x_677_);
v___x_685_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_664_, v_v_676_);
lean_dec(v_v_676_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
lean_inc_ref(v_a_665_);
v___x_687_ = l_Lean_indentExpr(v_a_665_);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_688_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref(v___x_689_);
v_a_680_ = v_a_690_;
goto v___jp_679_;
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v_bs_x27_678_);
lean_dec_ref(v_a_665_);
v_a_691_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_689_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_val_699_; 
v_val_699_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_val_699_);
lean_dec_ref(v___x_685_);
v_a_680_ = v_val_699_;
goto v___jp_679_;
}
v___jp_679_:
{
size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_i_667_, v___x_681_);
v___x_683_ = lean_array_uset(v_bs_x27_678_, v_i_667_, v_a_680_);
v_i_667_ = v___x_682_;
v_bs_668_ = v___x_683_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___boxed(lean_object* v_xs_700_, lean_object* v_a_701_, lean_object* v_sz_702_, lean_object* v_i_703_, lean_object* v_bs_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
size_t v_sz_boxed_710_; size_t v_i_boxed_711_; lean_object* v_res_712_; 
v_sz_boxed_710_ = lean_unbox_usize(v_sz_702_);
lean_dec(v_sz_702_);
v_i_boxed_711_ = lean_unbox_usize(v_i_703_);
lean_dec(v_i_703_);
v_res_712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_700_, v_a_701_, v_sz_boxed_710_, v_i_boxed_711_, v_bs_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v_xs_700_);
return v_res_712_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(lean_object* v_a_713_, lean_object* v_as_714_, size_t v_i_715_, size_t v_stop_716_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = lean_usize_dec_eq(v_i_715_, v_stop_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_array_uget_borrowed(v_as_714_, v_i_715_);
v___x_719_ = lean_expr_eqv(v_a_713_, v___x_718_);
if (v___x_719_ == 0)
{
size_t v___x_720_; size_t v___x_721_; 
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_add(v_i_715_, v___x_720_);
v_i_715_ = v___x_721_;
goto _start;
}
else
{
return v___x_719_;
}
}
else
{
uint8_t v___x_723_; 
v___x_723_ = 0;
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6___boxed(lean_object* v_a_724_, lean_object* v_as_725_, lean_object* v_i_726_, lean_object* v_stop_727_){
_start:
{
size_t v_i_boxed_728_; size_t v_stop_boxed_729_; uint8_t v_res_730_; lean_object* v_r_731_; 
v_i_boxed_728_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_stop_boxed_729_ = lean_unbox_usize(v_stop_727_);
lean_dec(v_stop_727_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(v_a_724_, v_as_725_, v_i_boxed_728_, v_stop_boxed_729_);
lean_dec_ref(v_as_725_);
lean_dec_ref(v_a_724_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(lean_object* v_as_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_array_get_size(v_as_732_);
v___x_736_ = lean_nat_dec_lt(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
return v___x_736_;
}
else
{
if (v___x_736_ == 0)
{
return v___x_736_;
}
else
{
size_t v___x_737_; size_t v___x_738_; uint8_t v___x_739_; 
v___x_737_ = ((size_t)0ULL);
v___x_738_ = lean_usize_of_nat(v___x_735_);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(v_a_733_, v_as_732_, v___x_737_, v___x_738_);
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4___boxed(lean_object* v_as_740_, lean_object* v_a_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(v_as_740_, v_a_741_);
lean_dec_ref(v_a_741_);
lean_dec_ref(v_as_740_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(lean_object* v_upperBound_744_, lean_object* v_xs_745_, lean_object* v_motive_746_, lean_object* v___x_747_, lean_object* v_baseDeclName_x3f_748_, lean_object* v___x_749_, lean_object* v_a_750_, lean_object* v_b_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_a_757_; uint8_t v___x_761_; 
v___x_761_ = lean_nat_dec_lt(v_a_750_, v_upperBound_744_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
lean_dec(v_a_750_);
lean_dec_ref(v___x_749_);
lean_dec(v_baseDeclName_x3f_748_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v_b_751_);
return v___x_762_;
}
else
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = lean_array_fget_borrowed(v_xs_745_, v_a_750_);
v___x_764_ = lean_expr_eqv(v___x_763_, v_motive_746_);
if (v___x_764_ == 0)
{
uint8_t v___x_765_; 
v___x_765_ = l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(v___x_747_, v___x_763_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = l_Lean_Expr_fvarId_x21(v___x_763_);
lean_inc_ref(v___y_752_);
v___x_767_ = l_Lean_FVarId_getDecl___redArg(v___x_766_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; uint8_t v___x_769_; uint8_t v___x_770_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref(v___x_767_);
v___x_769_ = l_Lean_LocalDecl_binderInfo(v_a_768_);
v___x_770_ = l_Lean_BinderInfo_isExplicit(v___x_769_);
if (v___x_770_ == 0)
{
lean_dec(v_a_768_);
v_a_757_ = v_b_751_;
goto v___jp_756_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_fst_774_; lean_object* v_snd_775_; lean_object* v___x_776_; lean_object* v___y_778_; 
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = l_Lean_LocalDecl_type(v_a_768_);
v___x_773_ = l_Lean_Meta_altArity(v_motive_746_, v___x_771_, v___x_772_);
lean_dec_ref(v___x_772_);
v_fst_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_fst_774_);
v_snd_775_ = lean_ctor_get(v___x_773_, 1);
lean_inc(v_snd_775_);
lean_dec_ref(v___x_773_);
v___x_776_ = l_Lean_LocalDecl_userName(v_a_768_);
lean_dec(v_a_768_);
if (lean_obj_tag(v_baseDeclName_x3f_748_) == 0)
{
v___y_778_ = v_baseDeclName_x3f_748_;
goto v___jp_777_;
}
else
{
lean_object* v_val_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_val_782_ = lean_ctor_get(v_baseDeclName_x3f_748_, 0);
lean_inc(v___x_776_);
lean_inc(v_val_782_);
v___x_783_ = l_Lean_Name_append(v_val_782_, v___x_776_);
lean_inc(v___x_783_);
lean_inc_ref(v___x_749_);
v___x_784_ = l_Lean_Environment_contains(v___x_749_, v___x_783_, v___x_770_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v___x_783_);
v___x_785_ = lean_box(0);
v___y_778_ = v___x_785_;
goto v___jp_777_;
}
else
{
lean_object* v___x_786_; 
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_783_);
v___y_778_ = v___x_786_;
goto v___jp_777_;
}
}
v___jp_777_:
{
lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_779_, 0, v___x_776_);
lean_ctor_set(v___x_779_, 1, v___y_778_);
lean_ctor_set(v___x_779_, 2, v_fst_774_);
v___x_780_ = lean_unbox(v_snd_775_);
lean_dec(v_snd_775_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*3, v___x_780_);
v___x_781_ = lean_array_push(v_b_751_, v___x_779_);
v_a_757_ = v___x_781_;
goto v___jp_756_;
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v_b_751_);
lean_dec(v_a_750_);
lean_dec_ref(v___x_749_);
lean_dec(v_baseDeclName_x3f_748_);
v_a_787_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_767_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_767_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
v_a_757_ = v_b_751_;
goto v___jp_756_;
}
}
else
{
v_a_757_ = v_b_751_;
goto v___jp_756_;
}
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = lean_nat_add(v_a_750_, v___x_758_);
lean_dec(v_a_750_);
v_a_750_ = v___x_759_;
v_b_751_ = v_a_757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg___boxed(lean_object* v_upperBound_795_, lean_object* v_xs_796_, lean_object* v_motive_797_, lean_object* v___x_798_, lean_object* v_baseDeclName_x3f_799_, lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v_b_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v_upperBound_795_, v_xs_796_, v_motive_797_, v___x_798_, v_baseDeclName_x3f_799_, v___x_800_, v_a_801_, v_b_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec_ref(v___x_798_);
lean_dec_ref(v_motive_797_);
lean_dec_ref(v_xs_796_);
lean_dec(v_upperBound_795_);
return v_res_807_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(lean_object* v_xs_814_, lean_object* v_a_815_, lean_object* v_elimExpr_816_, lean_object* v_baseDeclName_x3f_817_, lean_object* v_type_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; 
if (lean_obj_tag(v_x_819_) == 5)
{
lean_object* v_fn_902_; lean_object* v_arg_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_fn_902_ = lean_ctor_get(v_x_819_, 0);
lean_inc_ref(v_fn_902_);
v_arg_903_ = lean_ctor_get(v_x_819_, 1);
lean_inc_ref(v_arg_903_);
lean_dec_ref(v_x_819_);
v___x_904_ = lean_array_set(v_x_820_, v_x_821_, v_arg_903_);
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_sub(v_x_821_, v___x_905_);
lean_dec(v_x_821_);
v_x_819_ = v_fn_902_;
v_x_820_ = v___x_904_;
v_x_821_ = v___x_906_;
goto _start;
}
else
{
lean_object* v___f_908_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; uint8_t v___x_921_; 
lean_dec(v_x_821_);
v___f_908_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1));
v___x_921_ = l_Lean_Expr_isFVar(v_x_819_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v_x_820_);
lean_dec_ref(v_x_819_);
lean_dec(v_baseDeclName_x3f_817_);
lean_dec_ref(v_elimExpr_816_);
lean_dec_ref(v_a_815_);
v___x_922_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3);
v___x_923_ = l_Lean_indentExpr(v_type_818_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_924_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
else
{
lean_dec_ref(v_type_818_);
v___y_910_ = v___y_822_;
v___y_911_ = v___y_823_;
v___y_912_ = v___y_824_;
v___y_913_ = v___y_825_;
goto v___jp_909_;
}
v___jp_909_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_914_ = l_Array_takeWhile___redArg(v___f_908_, v_x_820_);
v___x_915_ = lean_array_get_size(v___x_914_);
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_array_get_size(v_x_820_);
v___x_918_ = lean_nat_dec_le(v___x_915_, v___x_916_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_915_);
lean_ctor_set(v___x_919_, 1, v___x_917_);
v___y_828_ = v___y_911_;
v___y_829_ = v___y_910_;
v___y_830_ = v___y_913_;
v___y_831_ = v___y_912_;
v___y_832_ = v___x_914_;
v___y_833_ = v___x_919_;
goto v___jp_827_;
}
else
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_916_);
lean_ctor_set(v___x_920_, 1, v___x_917_);
v___y_828_ = v___y_911_;
v___y_829_ = v___y_910_;
v___y_830_ = v___y_913_;
v___y_831_ = v___y_912_;
v___y_832_ = v___x_914_;
v___y_833_ = v___x_920_;
goto v___jp_827_;
}
}
}
v___jp_827_:
{
lean_object* v___x_834_; 
lean_inc(v___y_830_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_829_);
lean_inc_ref(v_x_819_);
v___x_834_ = lean_infer_type(v_x_819_, v___y_829_, v___y_828_, v___y_831_, v___y_830_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___f_836_; uint8_t v___x_837_; lean_object* v___x_838_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref(v___x_834_);
lean_inc_ref(v_x_820_);
lean_inc(v_a_835_);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed), 9, 2);
lean_closure_set(v___f_836_, 0, v_a_835_);
lean_closure_set(v___f_836_, 1, v_x_820_);
v___x_837_ = 0;
v___x_838_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_835_, v___f_836_, v___x_837_, v___x_837_, v___y_829_, v___y_828_, v___y_831_, v___y_830_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_839_; 
lean_dec_ref(v___x_838_);
v___x_839_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_814_, v_x_819_);
if (lean_obj_tag(v___x_839_) == 1)
{
lean_object* v_val_840_; size_t v_sz_841_; size_t v___x_842_; lean_object* v___x_843_; 
v_val_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_val_840_);
lean_dec_ref(v___x_839_);
v_sz_841_ = lean_array_size(v___y_832_);
v___x_842_ = ((size_t)0ULL);
lean_inc_ref(v___y_832_);
lean_inc_ref(v_a_815_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_814_, v_a_815_, v_sz_841_, v___x_842_, v___y_832_, v___y_829_, v___y_828_, v___y_831_, v___y_830_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v_lower_846_; lean_object* v_upper_847_; lean_object* v_env_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref(v___x_843_);
v___x_845_ = lean_st_ref_get(v___y_830_);
v_lower_846_ = lean_ctor_get(v___y_833_, 0);
lean_inc(v_lower_846_);
v_upper_847_ = lean_ctor_get(v___y_833_, 1);
lean_inc(v_upper_847_);
lean_dec_ref(v___y_833_);
v_env_848_ = lean_ctor_get(v___x_845_, 0);
lean_inc_ref(v_env_848_);
lean_dec(v___x_845_);
v___x_849_ = lean_array_get_size(v_xs_814_);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0));
v___x_852_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v___x_849_, v_xs_814_, v_x_819_, v___y_832_, v_baseDeclName_x3f_817_, v_env_848_, v___x_850_, v___x_851_, v___y_829_, v___y_831_, v___y_830_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_x_819_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_865_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_865_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_865_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_865_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v_start_858_; lean_object* v_stop_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_857_ = l_Array_toSubarray___redArg(v_x_820_, v_lower_846_, v_upper_847_);
v_start_858_ = lean_ctor_get(v___x_857_, 1);
lean_inc(v_start_858_);
v_stop_859_ = lean_ctor_get(v___x_857_, 2);
lean_inc(v_stop_859_);
lean_dec_ref(v___x_857_);
v___x_860_ = lean_nat_sub(v_stop_859_, v_start_858_);
lean_dec(v_start_858_);
lean_dec(v_stop_859_);
v___x_861_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_861_, 0, v_elimExpr_816_);
lean_ctor_set(v___x_861_, 1, v_a_815_);
lean_ctor_set(v___x_861_, 2, v_val_840_);
lean_ctor_set(v___x_861_, 3, v_a_844_);
lean_ctor_set(v___x_861_, 4, v_a_853_);
lean_ctor_set(v___x_861_, 5, v___x_860_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_861_);
v___x_863_ = v___x_855_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_upper_847_);
lean_dec(v_lower_846_);
lean_dec(v_a_844_);
lean_dec(v_val_840_);
lean_dec_ref(v_x_820_);
lean_dec_ref(v_elimExpr_816_);
lean_dec_ref(v_a_815_);
v_a_866_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_852_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_852_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_val_840_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_x_820_);
lean_dec_ref(v_x_819_);
lean_dec(v_baseDeclName_x3f_817_);
lean_dec_ref(v_elimExpr_816_);
lean_dec_ref(v_a_815_);
v_a_874_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_843_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_843_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec(v___x_839_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_x_820_);
lean_dec_ref(v_x_819_);
lean_dec(v_baseDeclName_x3f_817_);
lean_dec_ref(v_elimExpr_816_);
v___x_882_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
v___x_883_ = l_Lean_indentExpr(v_a_815_);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_884_, v___y_829_, v___y_828_, v___y_831_, v___y_830_);
return v___x_885_;
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_x_820_);
lean_dec_ref(v_x_819_);
lean_dec(v_baseDeclName_x3f_817_);
lean_dec_ref(v_elimExpr_816_);
lean_dec_ref(v_a_815_);
v_a_886_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_838_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_838_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
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
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_x_820_);
lean_dec_ref(v_x_819_);
lean_dec(v_baseDeclName_x3f_817_);
lean_dec_ref(v_elimExpr_816_);
lean_dec_ref(v_a_815_);
v_a_894_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_834_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_834_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___boxed(lean_object* v_xs_934_, lean_object* v_a_935_, lean_object* v_elimExpr_936_, lean_object* v_baseDeclName_x3f_937_, lean_object* v_type_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(v_xs_934_, v_a_935_, v_elimExpr_936_, v_baseDeclName_x3f_937_, v_type_938_, v_x_939_, v_x_940_, v_x_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec_ref(v_xs_934_);
return v_res_947_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0(void){
_start:
{
lean_object* v___x_948_; lean_object* v_dummy_949_; 
v___x_948_ = lean_box(0);
v_dummy_949_ = l_Lean_Expr_sort___override(v___x_948_);
return v_dummy_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0(lean_object* v_a_950_, lean_object* v_elimExpr_951_, lean_object* v_baseDeclName_x3f_952_, lean_object* v_xs_953_, lean_object* v_type_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_dummy_960_; lean_object* v_nargs_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_dummy_960_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___lam__0___closed__0, &l_Lean_Meta_getElimExprInfo___lam__0___closed__0_once, _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0);
v_nargs_961_ = l_Lean_Expr_getAppNumArgs(v_type_954_);
lean_inc(v_nargs_961_);
v___x_962_ = lean_mk_array(v_nargs_961_, v_dummy_960_);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = lean_nat_sub(v_nargs_961_, v___x_963_);
lean_dec(v_nargs_961_);
lean_inc_ref(v_type_954_);
v___x_965_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(v_xs_953_, v_a_950_, v_elimExpr_951_, v_baseDeclName_x3f_952_, v_type_954_, v_type_954_, v___x_962_, v___x_964_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0___boxed(lean_object* v_a_966_, lean_object* v_elimExpr_967_, lean_object* v_baseDeclName_x3f_968_, lean_object* v_xs_969_, lean_object* v_type_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Meta_getElimExprInfo___lam__0(v_a_966_, v_elimExpr_967_, v_baseDeclName_x3f_968_, v_xs_969_, v_type_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec_ref(v_xs_969_);
return v_res_976_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_977_; double v___x_978_; 
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_float_of_nat(v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8(lean_object* v_cls_982_, lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_ref_989_; lean_object* v___x_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1035_; 
v_ref_989_ = lean_ctor_get(v___y_986_, 5);
v___x_990_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1035_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1035_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v_traceState_996_; lean_object* v_env_997_; lean_object* v_nextMacroScope_998_; lean_object* v_ngen_999_; lean_object* v_auxDeclNGen_1000_; lean_object* v_cache_1001_; lean_object* v_messages_1002_; lean_object* v_infoState_1003_; lean_object* v_snapshotTasks_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1034_; 
v___x_995_ = lean_st_ref_take(v___y_987_);
v_traceState_996_ = lean_ctor_get(v___x_995_, 4);
v_env_997_ = lean_ctor_get(v___x_995_, 0);
v_nextMacroScope_998_ = lean_ctor_get(v___x_995_, 1);
v_ngen_999_ = lean_ctor_get(v___x_995_, 2);
v_auxDeclNGen_1000_ = lean_ctor_get(v___x_995_, 3);
v_cache_1001_ = lean_ctor_get(v___x_995_, 5);
v_messages_1002_ = lean_ctor_get(v___x_995_, 6);
v_infoState_1003_ = lean_ctor_get(v___x_995_, 7);
v_snapshotTasks_1004_ = lean_ctor_get(v___x_995_, 8);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1006_ = v___x_995_;
v_isShared_1007_ = v_isSharedCheck_1034_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_snapshotTasks_1004_);
lean_inc(v_infoState_1003_);
lean_inc(v_messages_1002_);
lean_inc(v_cache_1001_);
lean_inc(v_traceState_996_);
lean_inc(v_auxDeclNGen_1000_);
lean_inc(v_ngen_999_);
lean_inc(v_nextMacroScope_998_);
lean_inc(v_env_997_);
lean_dec(v___x_995_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1034_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
uint64_t v_tid_1008_; lean_object* v_traces_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1033_; 
v_tid_1008_ = lean_ctor_get_uint64(v_traceState_996_, sizeof(void*)*1);
v_traces_1009_ = lean_ctor_get(v_traceState_996_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_traceState_996_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1011_ = v_traceState_996_;
v_isShared_1012_ = v_isSharedCheck_1033_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_traces_1009_);
lean_dec(v_traceState_996_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1033_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; double v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__0, &l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__0);
v___x_1015_ = 0;
v___x_1016_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__1));
v___x_1017_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1017_, 0, v_cls_982_);
lean_ctor_set(v___x_1017_, 1, v___x_1013_);
lean_ctor_set(v___x_1017_, 2, v___x_1016_);
lean_ctor_set_float(v___x_1017_, sizeof(void*)*3, v___x_1014_);
lean_ctor_set_float(v___x_1017_, sizeof(void*)*3 + 8, v___x_1014_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*3 + 16, v___x_1015_);
v___x_1018_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___closed__2));
v___x_1019_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v_a_991_);
lean_ctor_set(v___x_1019_, 2, v___x_1018_);
lean_inc(v_ref_989_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v_ref_989_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_PersistentArray_push___redArg(v_traces_1009_, v___x_1020_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1021_);
v___x_1023_ = v___x_1011_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1021_);
lean_ctor_set_uint64(v_reuseFailAlloc_1032_, sizeof(void*)*1, v_tid_1008_);
v___x_1023_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1025_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 4, v___x_1023_);
v___x_1025_ = v___x_1006_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_env_997_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_nextMacroScope_998_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_ngen_999_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_auxDeclNGen_1000_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1031_, 5, v_cache_1001_);
lean_ctor_set(v_reuseFailAlloc_1031_, 6, v_messages_1002_);
lean_ctor_set(v_reuseFailAlloc_1031_, 7, v_infoState_1003_);
lean_ctor_set(v_reuseFailAlloc_1031_, 8, v_snapshotTasks_1004_);
v___x_1025_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1026_ = lean_st_ref_set(v___y_987_, v___x_1025_);
v___x_1027_ = lean_box(0);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1027_);
v___x_1029_ = v___x_993_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8___boxed(lean_object* v_cls_1036_, lean_object* v_msg_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8(v_cls_1036_, v_msg_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1043_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__4(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__3));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__6(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__5));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo(lean_object* v_elimExpr_1055_, lean_object* v_baseDeclName_x3f_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1062_; 
lean_inc(v_a_1060_);
lean_inc_ref(v_a_1059_);
lean_inc(v_a_1058_);
lean_inc_ref(v_a_1057_);
lean_inc_ref(v_elimExpr_1055_);
v___x_1062_ = lean_infer_type(v_elimExpr_1055_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_a_1066_; lean_object* v___f_1067_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; uint8_t v___x_1075_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__2));
v___x_1065_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_getElimExprInfo_spec__7___redArg(v___x_1064_, v_a_1059_);
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
lean_inc_ref(v_elimExpr_1055_);
lean_inc(v_a_1063_);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_Meta_getElimExprInfo___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1067_, 0, v_a_1063_);
lean_closure_set(v___f_1067_, 1, v_elimExpr_1055_);
lean_closure_set(v___f_1067_, 2, v_baseDeclName_x3f_1056_);
v___x_1075_ = lean_unbox(v_a_1066_);
lean_dec(v_a_1066_);
if (v___x_1075_ == 0)
{
lean_dec_ref(v_elimExpr_1055_);
v___y_1069_ = v_a_1057_;
v___y_1070_ = v_a_1058_;
v___y_1071_ = v_a_1059_;
v___y_1072_ = v_a_1060_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1076_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__4, &l_Lean_Meta_getElimExprInfo___closed__4_once, _init_l_Lean_Meta_getElimExprInfo___closed__4);
v___x_1077_ = l_Lean_indentExpr(v_elimExpr_1055_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__6, &l_Lean_Meta_getElimExprInfo___closed__6_once, _init_l_Lean_Meta_getElimExprInfo___closed__6);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
lean_inc(v_a_1063_);
v___x_1081_ = l_Lean_indentExpr(v_a_1063_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__8(v___x_1064_, v___x_1082_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_dec_ref(v___x_1083_);
v___y_1069_ = v_a_1057_;
v___y_1070_ = v_a_1058_;
v___y_1071_ = v_a_1059_;
v___y_1072_ = v_a_1060_;
goto v___jp_1068_;
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v___f_1067_);
lean_dec(v_a_1063_);
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
v___jp_1068_:
{
uint8_t v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = 0;
v___x_1074_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_1063_, v___f_1067_, v___x_1073_, v___x_1073_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
return v___x_1074_;
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_baseDeclName_x3f_1056_);
lean_dec_ref(v_elimExpr_1055_);
v_a_1092_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1062_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1062_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___boxed(lean_object* v_elimExpr_1100_, lean_object* v_baseDeclName_x3f_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_Meta_getElimExprInfo(v_elimExpr_1100_, v_baseDeclName_x3f_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(lean_object* v_00_u03b1_1108_, lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_msg_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(v_00_u03b1_1116_, v_msg_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(lean_object* v_upperBound_1124_, lean_object* v_xs_1125_, lean_object* v_motive_1126_, lean_object* v___x_1127_, lean_object* v_baseDeclName_x3f_1128_, lean_object* v___x_1129_, lean_object* v_inst_1130_, lean_object* v_R_1131_, lean_object* v_a_1132_, lean_object* v_b_1133_, lean_object* v_c_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v_upperBound_1124_, v_xs_1125_, v_motive_1126_, v___x_1127_, v_baseDeclName_x3f_1128_, v___x_1129_, v_a_1132_, v_b_1133_, v___y_1135_, v___y_1137_, v___y_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___boxed(lean_object* v_upperBound_1141_, lean_object* v_xs_1142_, lean_object* v_motive_1143_, lean_object* v___x_1144_, lean_object* v_baseDeclName_x3f_1145_, lean_object* v___x_1146_, lean_object* v_inst_1147_, lean_object* v_R_1148_, lean_object* v_a_1149_, lean_object* v_b_1150_, lean_object* v_c_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(v_upperBound_1141_, v_xs_1142_, v_motive_1143_, v___x_1144_, v_baseDeclName_x3f_1145_, v___x_1146_, v_inst_1147_, v_R_1148_, v_a_1149_, v_b_1150_, v_c_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_motive_1143_);
lean_dec_ref(v_xs_1142_);
lean_dec(v_upperBound_1141_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object* v_elimName_1158_, lean_object* v_baseDeclName_x3f_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_elimName_1158_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = l_Lean_Meta_getElimExprInfo(v_a_1166_, v_baseDeclName_x3f_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
return v___x_1167_;
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v_baseDeclName_x3f_1159_);
v_a_1168_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1165_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1165_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___boxed(lean_object* v_elimName_1176_, lean_object* v_baseDeclName_x3f_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Meta_getElimInfo(v_elimName_1176_, v_baseDeclName_x3f_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(lean_object* v_a_1184_, lean_object* v_as_1185_, size_t v_i_1186_, size_t v_stop_1187_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_usize_dec_eq(v_i_1186_, v_stop_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_array_uget_borrowed(v_as_1185_, v_i_1186_);
v___x_1190_ = lean_nat_dec_eq(v_a_1184_, v___x_1189_);
if (v___x_1190_ == 0)
{
size_t v___x_1191_; size_t v___x_1192_; 
v___x_1191_ = ((size_t)1ULL);
v___x_1192_ = lean_usize_add(v_i_1186_, v___x_1191_);
v_i_1186_ = v___x_1192_;
goto _start;
}
else
{
return v___x_1190_;
}
}
else
{
uint8_t v___x_1194_; 
v___x_1194_ = 0;
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0___boxed(lean_object* v_a_1195_, lean_object* v_as_1196_, lean_object* v_i_1197_, lean_object* v_stop_1198_){
_start:
{
size_t v_i_boxed_1199_; size_t v_stop_boxed_1200_; uint8_t v_res_1201_; lean_object* v_r_1202_; 
v_i_boxed_1199_ = lean_unbox_usize(v_i_1197_);
lean_dec(v_i_1197_);
v_stop_boxed_1200_ = lean_unbox_usize(v_stop_1198_);
lean_dec(v_stop_1198_);
v_res_1201_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_1195_, v_as_1196_, v_i_boxed_1199_, v_stop_boxed_1200_);
lean_dec_ref(v_as_1196_);
lean_dec(v_a_1195_);
v_r_1202_ = lean_box(v_res_1201_);
return v_r_1202_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(lean_object* v_as_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_array_get_size(v_as_1203_);
v___x_1207_ = lean_nat_dec_lt(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
return v___x_1207_;
}
else
{
if (v___x_1207_ == 0)
{
return v___x_1207_;
}
else
{
size_t v___x_1208_; size_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = ((size_t)0ULL);
v___x_1209_ = lean_usize_of_nat(v___x_1206_);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_1204_, v_as_1203_, v___x_1208_, v___x_1209_);
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0___boxed(lean_object* v_as_1211_, lean_object* v_a_1212_){
_start:
{
uint8_t v_res_1213_; lean_object* v_r_1214_; 
v_res_1213_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_as_1211_, v_a_1212_);
lean_dec(v_a_1212_);
lean_dec_ref(v_as_1211_);
v_r_1214_ = lean_box(v_res_1213_);
return v_r_1214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1));
v___x_1219_ = l_Lean_stringToMessageData(v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3));
v___x_1222_ = l_Lean_stringToMessageData(v___x_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5));
v___x_1225_ = l_Lean_stringToMessageData(v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7));
v___x_1228_ = l_Lean_stringToMessageData(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9));
v___x_1231_ = l_Lean_stringToMessageData(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(lean_object* v_elimInfo_1232_, lean_object* v_targets_1233_, lean_object* v_type_1234_, lean_object* v_argIdx_1235_, lean_object* v_targetIdx_1236_, lean_object* v_implicits_1237_, lean_object* v_targets_x27_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Meta_whnfD(v_type_1234_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref(v___x_1247_);
if (lean_obj_tag(v_a_1248_) == 7)
{
lean_object* v_binderName_1249_; lean_object* v_binderType_1250_; lean_object* v_body_1251_; uint8_t v_binderInfo_1252_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v_elimExpr_1320_; lean_object* v_targetsPos_1321_; uint8_t v___x_1322_; 
v_binderName_1249_ = lean_ctor_get(v_a_1248_, 0);
lean_inc(v_binderName_1249_);
v_binderType_1250_ = lean_ctor_get(v_a_1248_, 1);
lean_inc_ref(v_binderType_1250_);
v_body_1251_ = lean_ctor_get(v_a_1248_, 2);
lean_inc_ref(v_body_1251_);
v_binderInfo_1252_ = lean_ctor_get_uint8(v_a_1248_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_1248_);
v_elimExpr_1320_ = lean_ctor_get(v_elimInfo_1232_, 0);
v_targetsPos_1321_ = lean_ctor_get(v_elimInfo_1232_, 3);
v___x_1322_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_targetsPos_1321_, v_argIdx_1235_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec(v_binderName_1249_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_binderType_1250_);
v___x_1324_ = 0;
v___x_1325_ = lean_box(0);
v___x_1326_ = l_Lean_Meta_mkFreshExprMVar(v___x_1323_, v___x_1324_, v___x_1325_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = lean_expr_instantiate1(v_body_1251_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_body_1251_);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_nat_add(v_argIdx_1235_, v___x_1329_);
lean_dec(v_argIdx_1235_);
v_type_1234_ = v___x_1328_;
v_argIdx_1235_ = v___x_1330_;
goto _start;
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v_body_1251_);
lean_dec_ref(v_targets_x27_1238_);
lean_dec_ref(v_implicits_1237_);
lean_dec(v_targetIdx_1236_);
lean_dec(v_argIdx_1235_);
lean_dec_ref(v_elimInfo_1232_);
v_a_1332_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1326_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1326_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
uint8_t v___x_1340_; 
v___x_1340_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1252_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_binderType_1250_);
v___x_1342_ = 0;
v___x_1343_ = l_Lean_Meta_mkFreshExprMVar(v___x_1341_, v___x_1342_, v_binderName_1249_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1343_);
v___x_1345_ = lean_expr_instantiate1(v_body_1251_, v_a_1344_);
lean_dec_ref(v_body_1251_);
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_add(v_argIdx_1235_, v___x_1346_);
lean_dec(v_argIdx_1235_);
v___x_1348_ = l_Lean_Expr_mvarId_x21(v_a_1344_);
v___x_1349_ = lean_array_push(v_implicits_1237_, v___x_1348_);
v___x_1350_ = lean_array_push(v_targets_x27_1238_, v_a_1344_);
v_type_1234_ = v___x_1345_;
v_argIdx_1235_ = v___x_1347_;
v_implicits_1237_ = v___x_1349_;
v_targets_x27_1238_ = v___x_1350_;
goto _start;
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v_body_1251_);
lean_dec_ref(v_targets_x27_1238_);
lean_dec_ref(v_implicits_1237_);
lean_dec(v_targetIdx_1236_);
lean_dec(v_argIdx_1235_);
lean_dec_ref(v_elimInfo_1232_);
v_a_1352_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1343_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1343_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
lean_dec(v_binderName_1249_);
v___x_1360_ = lean_array_get_size(v_targets_1233_);
v___x_1361_ = lean_nat_dec_lt(v_targetIdx_1236_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1362_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6);
lean_inc_ref(v_elimExpr_1320_);
v___x_1363_ = l_Lean_MessageData_ofExpr(v_elimExpr_1320_);
v___x_1364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1366_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_dec_ref(v___x_1367_);
v___y_1266_ = v_a_1239_;
v___y_1267_ = v_a_1240_;
v___y_1268_ = v_a_1241_;
v___y_1269_ = v_a_1242_;
goto v___jp_1265_;
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v_body_1251_);
lean_dec_ref(v_binderType_1250_);
lean_dec_ref(v_targets_x27_1238_);
lean_dec_ref(v_implicits_1237_);
lean_dec(v_targetIdx_1236_);
lean_dec(v_argIdx_1235_);
lean_dec_ref(v_elimInfo_1232_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
v___y_1266_ = v_a_1239_;
v___y_1267_ = v_a_1240_;
v___y_1268_ = v_a_1241_;
v___y_1269_ = v_a_1242_;
goto v___jp_1265_;
}
}
}
v___jp_1253_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1259_ = lean_expr_instantiate1(v_body_1251_, v___y_1254_);
lean_dec_ref(v_body_1251_);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_add(v_argIdx_1235_, v___x_1260_);
lean_dec(v_argIdx_1235_);
v___x_1262_ = lean_nat_add(v_targetIdx_1236_, v___x_1260_);
lean_dec(v_targetIdx_1236_);
v___x_1263_ = lean_array_push(v_targets_x27_1238_, v___y_1254_);
v_type_1234_ = v___x_1259_;
v_argIdx_1235_ = v___x_1261_;
v_targetIdx_1236_ = v___x_1262_;
v_targets_x27_1238_ = v___x_1263_;
v_a_1239_ = v___y_1255_;
v_a_1240_ = v___y_1256_;
v_a_1241_ = v___y_1257_;
v_a_1242_ = v___y_1258_;
goto _start;
}
v___jp_1265_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = l_Lean_instInhabitedExpr;
v___x_1271_ = lean_array_get_borrowed(v___x_1270_, v_targets_1233_, v_targetIdx_1236_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
lean_inc(v___x_1271_);
v___x_1272_ = lean_infer_type(v___x_1271_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref(v___x_1272_);
lean_inc(v_a_1273_);
lean_inc_ref(v_binderType_1250_);
v___x_1274_ = l_Lean_Meta_isExprDefEq(v_binderType_1250_, v_a_1273_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; uint8_t v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1274_);
v___x_1276_ = lean_unbox(v_a_1275_);
lean_dec(v_a_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_box(0);
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0));
v___x_1279_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_1273_, v_binderType_1250_, v___x_1277_, v___x_1278_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2);
lean_inc(v___x_1271_);
v___x_1282_ = l_Lean_indentExpr(v___x_1271_);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v_a_1280_);
v___x_1287_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1286_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_dec_ref(v___x_1287_);
lean_inc(v___x_1271_);
v___y_1254_ = v___x_1271_;
v___y_1255_ = v___y_1266_;
v___y_1256_ = v___y_1267_;
v___y_1257_ = v___y_1268_;
v___y_1258_ = v___y_1269_;
goto v___jp_1253_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_body_1251_);
lean_dec_ref(v_targets_x27_1238_);
lean_dec_ref(v_implicits_1237_);
lean_dec(v_targetIdx_1236_);
lean_dec(v_argIdx_1235_);
lean_dec_ref(v_elimInfo_1232_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
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
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_body_1251_);
lean_dec_ref(v_targets_x27_1238_);
lean_dec_ref(v_implicits_1237_);
lean_dec(v_targetIdx_1236_);
lean_dec(v_argIdx_1235_);
lean_dec_ref(v_elimInfo_1232_);
v_a_1296_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1279_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1279_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
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
else
{
lean_dec(v_a_1273_);
lean_dec_ref(v_binderType_1250_);
lean_inc(v___x_1271_);
v___y_1254_ = v___x_1271_;
v___y_1255_ = v___y_1266_;
v___y_1256_ = v___y_1267_;
v___y_1257_ = v___y_1268_;
v___y_1258_ = v___y_1269_;
goto v___jp_1253_;
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_a_1273_);
lean_dec_ref(v_body_1251_);
lean_dec_ref(v_binderType_1250_);
lean_dec_ref(v_targets_x27_1238_);
lean_dec_ref(v_implicits_1237_);
lean_dec(v_targetIdx_1236_);
lean_dec(v_argIdx_1235_);
lean_dec_ref(v_elimInfo_1232_);
v_a_1304_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1274_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1274_);
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
lean_dec_ref(v_body_1251_);
lean_dec_ref(v_binderType_1250_);
lean_dec_ref(v_targets_x27_1238_);
lean_dec_ref(v_implicits_1237_);
lean_dec(v_targetIdx_1236_);
lean_dec(v_argIdx_1235_);
lean_dec_ref(v_elimInfo_1232_);
v_a_1312_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1272_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1272_);
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
}
else
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
lean_dec(v_a_1248_);
lean_dec(v_argIdx_1235_);
v___x_1376_ = lean_array_get_size(v_targets_1233_);
v___x_1377_ = lean_nat_dec_eq(v_targetIdx_1236_, v___x_1376_);
lean_dec(v_targetIdx_1236_);
if (v___x_1377_ == 0)
{
lean_object* v_elimExpr_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_elimExpr_1378_ = lean_ctor_get(v_elimInfo_1232_, 0);
lean_inc_ref(v_elimExpr_1378_);
lean_dec_ref(v_elimInfo_1232_);
v___x_1379_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10);
v___x_1380_ = l_Lean_MessageData_ofExpr(v_elimExpr_1378_);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1383_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_dec_ref(v___x_1384_);
goto v___jp_1244_;
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v_targets_x27_1238_);
lean_dec_ref(v_implicits_1237_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_dec_ref(v_elimInfo_1232_);
goto v___jp_1244_;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v_targets_x27_1238_);
lean_dec_ref(v_implicits_1237_);
lean_dec(v_targetIdx_1236_);
lean_dec(v_argIdx_1235_);
lean_dec_ref(v_elimInfo_1232_);
v_a_1393_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1247_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1247_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
v___jp_1244_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v_implicits_1237_);
lean_ctor_set(v___x_1245_, 1, v_targets_x27_1238_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___boxed(lean_object* v_elimInfo_1401_, lean_object* v_targets_1402_, lean_object* v_type_1403_, lean_object* v_argIdx_1404_, lean_object* v_targetIdx_1405_, lean_object* v_implicits_1406_, lean_object* v_targets_x27_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(v_elimInfo_1401_, v_targets_1402_, v_type_1403_, v_argIdx_1404_, v_targetIdx_1405_, v_implicits_1406_, v_targets_x27_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec_ref(v_targets_1402_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(lean_object* v_e_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = l_Lean_Expr_hasMVar(v_e_1414_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_e_1414_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; lean_object* v_mctx_1420_; lean_object* v___x_1421_; lean_object* v_fst_1422_; lean_object* v_snd_1423_; lean_object* v___x_1424_; lean_object* v_cache_1425_; lean_object* v_zetaDeltaFVarIds_1426_; lean_object* v_postponed_1427_; lean_object* v_diag_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1437_; 
v___x_1419_ = lean_st_ref_get(v___y_1415_);
v_mctx_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_ref(v_mctx_1420_);
lean_dec(v___x_1419_);
v___x_1421_ = l_Lean_instantiateMVarsCore(v_mctx_1420_, v_e_1414_);
v_fst_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_fst_1422_);
v_snd_1423_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_snd_1423_);
lean_dec_ref(v___x_1421_);
v___x_1424_ = lean_st_ref_take(v___y_1415_);
v_cache_1425_ = lean_ctor_get(v___x_1424_, 1);
v_zetaDeltaFVarIds_1426_ = lean_ctor_get(v___x_1424_, 2);
v_postponed_1427_ = lean_ctor_get(v___x_1424_, 3);
v_diag_1428_ = lean_ctor_get(v___x_1424_, 4);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v___x_1424_, 0);
lean_dec(v_unused_1438_);
v___x_1430_ = v___x_1424_;
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_diag_1428_);
lean_inc(v_postponed_1427_);
lean_inc(v_zetaDeltaFVarIds_1426_);
lean_inc(v_cache_1425_);
lean_dec(v___x_1424_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v_snd_1423_);
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_snd_1423_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_cache_1425_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_zetaDeltaFVarIds_1426_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_postponed_1427_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v_diag_1428_);
v___x_1433_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_st_ref_set(v___y_1415_, v___x_1433_);
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_fst_1422_);
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg___boxed(lean_object* v_e_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_e_1439_, v___y_1440_);
lean_dec(v___y_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(lean_object* v_e_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_e_1443_, v___y_1445_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___boxed(lean_object* v_e_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(v_e_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1457_, lean_object* v_i_1458_, lean_object* v_k_1459_){
_start:
{
lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1460_ = lean_array_get_size(v_keys_1457_);
v___x_1461_ = lean_nat_dec_lt(v_i_1458_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_dec(v_i_1458_);
return v___x_1461_;
}
else
{
lean_object* v_k_x27_1462_; uint8_t v___x_1463_; 
v_k_x27_1462_ = lean_array_fget_borrowed(v_keys_1457_, v_i_1458_);
v___x_1463_ = l_Lean_instBEqMVarId_beq(v_k_1459_, v_k_x27_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v_i_1458_, v___x_1464_);
lean_dec(v_i_1458_);
v_i_1458_ = v___x_1465_;
goto _start;
}
else
{
lean_dec(v_i_1458_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1467_, lean_object* v_i_1468_, lean_object* v_k_1469_){
_start:
{
uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_res_1470_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1467_, v_i_1468_, v_k_1469_);
lean_dec(v_k_1469_);
lean_dec_ref(v_keys_1467_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_1472_; size_t v___x_1473_; size_t v___x_1474_; 
v___x_1472_ = ((size_t)5ULL);
v___x_1473_ = ((size_t)1ULL);
v___x_1474_ = lean_usize_shift_left(v___x_1473_, v___x_1472_);
return v___x_1474_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1475_; size_t v___x_1476_; size_t v___x_1477_; 
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_1477_ = lean_usize_sub(v___x_1476_, v___x_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1478_, size_t v_x_1479_, lean_object* v_x_1480_){
_start:
{
if (lean_obj_tag(v_x_1478_) == 0)
{
lean_object* v_es_1481_; lean_object* v___x_1482_; size_t v___x_1483_; size_t v___x_1484_; size_t v___x_1485_; lean_object* v_j_1486_; lean_object* v___x_1487_; 
v_es_1481_ = lean_ctor_get(v_x_1478_, 0);
lean_inc_ref(v_es_1481_);
lean_dec_ref(v_x_1478_);
v___x_1482_ = lean_box(2);
v___x_1483_ = ((size_t)5ULL);
v___x_1484_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1485_ = lean_usize_land(v_x_1479_, v___x_1484_);
v_j_1486_ = lean_usize_to_nat(v___x_1485_);
v___x_1487_ = lean_array_get(v___x_1482_, v_es_1481_, v_j_1486_);
lean_dec(v_j_1486_);
lean_dec_ref(v_es_1481_);
switch(lean_obj_tag(v___x_1487_))
{
case 0:
{
lean_object* v_key_1488_; uint8_t v___x_1489_; 
v_key_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_key_1488_);
lean_dec_ref(v___x_1487_);
v___x_1489_ = l_Lean_instBEqMVarId_beq(v_x_1480_, v_key_1488_);
lean_dec(v_key_1488_);
return v___x_1489_;
}
case 1:
{
lean_object* v_node_1490_; size_t v___x_1491_; 
v_node_1490_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_node_1490_);
lean_dec_ref(v___x_1487_);
v___x_1491_ = lean_usize_shift_right(v_x_1479_, v___x_1483_);
v_x_1478_ = v_node_1490_;
v_x_1479_ = v___x_1491_;
goto _start;
}
default: 
{
uint8_t v___x_1493_; 
v___x_1493_ = 0;
return v___x_1493_;
}
}
}
else
{
lean_object* v_ks_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_ks_1494_ = lean_ctor_get(v_x_1478_, 0);
lean_inc_ref(v_ks_1494_);
lean_dec_ref(v_x_1478_);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1494_, v___x_1495_, v_x_1480_);
lean_dec_ref(v_ks_1494_);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
size_t v_x_3351__boxed_1500_; uint8_t v_res_1501_; lean_object* v_r_1502_; 
v_x_3351__boxed_1500_ = lean_unbox_usize(v_x_1498_);
lean_dec(v_x_1498_);
v_res_1501_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1497_, v_x_3351__boxed_1500_, v_x_1499_);
lean_dec(v_x_1499_);
v_r_1502_ = lean_box(v_res_1501_);
return v_r_1502_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(lean_object* v_x_1503_, lean_object* v_x_1504_){
_start:
{
uint64_t v___x_1505_; size_t v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = l_Lean_instHashableMVarId_hash(v_x_1504_);
v___x_1506_ = lean_uint64_to_usize(v___x_1505_);
v___x_1507_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1503_, v___x_1506_, v_x_1504_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg___boxed(lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
uint8_t v_res_1510_; lean_object* v_r_1511_; 
v_res_1510_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_1508_, v_x_1509_);
lean_dec(v_x_1509_);
v_r_1511_ = lean_box(v_res_1510_);
return v_r_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(lean_object* v_mvarId_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v_mctx_1516_; lean_object* v_eAssignment_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1515_ = lean_st_ref_get(v___y_1513_);
v_mctx_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc_ref(v_mctx_1516_);
lean_dec(v___x_1515_);
v_eAssignment_1517_ = lean_ctor_get(v_mctx_1516_, 7);
lean_inc_ref(v_eAssignment_1517_);
lean_dec_ref(v_mctx_1516_);
v___x_1518_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_eAssignment_1517_, v_mvarId_1512_);
v___x_1519_ = lean_box(v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg___boxed(lean_object* v_mvarId_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_mvarId_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec(v_mvarId_1521_);
return v_res_1524_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(lean_object* v_as_1531_, size_t v_sz_1532_, size_t v_i_1533_, lean_object* v_b_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_a_1541_; uint8_t v___x_1545_; 
v___x_1545_ = lean_usize_dec_lt(v_i_1533_, v_sz_1532_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v_b_1534_);
return v___x_1546_;
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1548_; 
v_a_1547_ = lean_array_uget_borrowed(v_as_1531_, v_i_1533_);
v___x_1548_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_a_1547_, v___y_1536_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1548_);
v___x_1550_ = lean_box(0);
v___x_1551_ = lean_unbox(v_a_1549_);
lean_dec(v_a_1549_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_inc(v_a_1547_);
v___x_1552_ = l_Lean_MVarId_getDecl(v_a_1547_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v_userName_1557_; uint8_t v___x_1558_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
v_userName_1557_ = lean_ctor_get(v_a_1553_, 0);
lean_inc(v_userName_1557_);
lean_dec(v_a_1553_);
v___x_1558_ = l_Lean_Name_isAnonymous(v_userName_1557_);
if (v___x_1558_ == 0)
{
uint8_t v___x_1559_; 
v___x_1559_ = l_Lean_Name_hasMacroScopes(v_userName_1557_);
lean_dec(v_userName_1557_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_inc(v_a_1547_);
v___x_1560_ = l_Lean_MVarId_getDecl(v_a_1547_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v_userName_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1560_);
v_userName_1562_ = lean_ctor_get(v_a_1561_, 0);
lean_inc(v_userName_1562_);
lean_dec(v_a_1561_);
v___x_1563_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3);
v___x_1564_ = l_Lean_MessageData_ofName(v_userName_1562_);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1567_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_dec_ref(v___x_1568_);
v_a_1541_ = v___x_1550_;
goto v___jp_1540_;
}
else
{
return v___x_1568_;
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1560_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1560_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
goto v___jp_1554_;
}
}
else
{
lean_dec(v_userName_1557_);
goto v___jp_1554_;
}
v___jp_1554_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1);
v___x_1556_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1555_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_dec_ref(v___x_1556_);
v_a_1541_ = v___x_1550_;
goto v___jp_1540_;
}
else
{
return v___x_1556_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_a_1577_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1552_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1552_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
v_a_1541_ = v___x_1550_;
goto v___jp_1540_;
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1585_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1548_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1548_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
v___jp_1540_:
{
size_t v___x_1542_; size_t v___x_1543_; 
v___x_1542_ = ((size_t)1ULL);
v___x_1543_ = lean_usize_add(v_i_1533_, v___x_1542_);
v_i_1533_ = v___x_1543_;
v_b_1534_ = v_a_1541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___boxed(lean_object* v_as_1593_, lean_object* v_sz_1594_, lean_object* v_i_1595_, lean_object* v_b_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
size_t v_sz_boxed_1602_; size_t v_i_boxed_1603_; lean_object* v_res_1604_; 
v_sz_boxed_1602_ = lean_unbox_usize(v_sz_1594_);
lean_dec(v_sz_1594_);
v_i_boxed_1603_ = lean_unbox_usize(v_i_1595_);
lean_dec(v_i_1595_);
v_res_1604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_as_1593_, v_sz_boxed_1602_, v_i_boxed_1603_, v_b_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec_ref(v_as_1593_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(size_t v_sz_1605_, size_t v_i_1606_, lean_object* v_bs_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_usize_dec_lt(v_i_1606_, v_sz_1605_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v_bs_1607_);
return v___x_1614_;
}
else
{
lean_object* v_v_1615_; lean_object* v___x_1616_; 
v_v_1615_ = lean_array_uget_borrowed(v_bs_1607_, v_i_1606_);
lean_inc(v_v_1615_);
v___x_1616_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_v_1615_, v___y_1609_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v_bs_x27_1619_; size_t v___x_1620_; size_t v___x_1621_; lean_object* v___x_1622_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = lean_unsigned_to_nat(0u);
v_bs_x27_1619_ = lean_array_uset(v_bs_1607_, v_i_1606_, v___x_1618_);
v___x_1620_ = ((size_t)1ULL);
v___x_1621_ = lean_usize_add(v_i_1606_, v___x_1620_);
v___x_1622_ = lean_array_uset(v_bs_x27_1619_, v_i_1606_, v_a_1617_);
v_i_1606_ = v___x_1621_;
v_bs_1607_ = v___x_1622_;
goto _start;
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_bs_1607_);
v_a_1624_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1616_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1616_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3___boxed(lean_object* v_sz_1632_, lean_object* v_i_1633_, lean_object* v_bs_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
size_t v_sz_boxed_1640_; size_t v_i_boxed_1641_; lean_object* v_res_1642_; 
v_sz_boxed_1640_ = lean_unbox_usize(v_sz_1632_);
lean_dec(v_sz_1632_);
v_i_boxed_1641_ = lean_unbox_usize(v_i_1633_);
lean_dec(v_i_1633_);
v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_boxed_1640_, v_i_boxed_1641_, v_bs_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object* v_elimInfo_1645_, lean_object* v_targets_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_elimType_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_elimType_1652_ = lean_ctor_get(v_elimInfo_1645_, 1);
lean_inc_ref(v_elimType_1652_);
v___x_1653_ = lean_unsigned_to_nat(0u);
v___x_1654_ = ((lean_object*)(l_Lean_Meta_addImplicitTargets___closed__0));
v___x_1655_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(v_elimInfo_1645_, v_targets_1646_, v_elimType_1652_, v___x_1653_, v___x_1653_, v___x_1654_, v___x_1654_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v_fst_1657_; lean_object* v_snd_1658_; lean_object* v___x_1659_; size_t v_sz_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v___x_1655_);
v_fst_1657_ = lean_ctor_get(v_a_1656_, 0);
lean_inc(v_fst_1657_);
v_snd_1658_ = lean_ctor_get(v_a_1656_, 1);
lean_inc(v_snd_1658_);
lean_dec(v_a_1656_);
v___x_1659_ = lean_box(0);
v_sz_1660_ = lean_array_size(v_fst_1657_);
v___x_1661_ = ((size_t)0ULL);
v___x_1662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_fst_1657_, v_sz_1660_, v___x_1661_, v___x_1659_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_fst_1657_);
if (lean_obj_tag(v___x_1662_) == 0)
{
size_t v_sz_1663_; lean_object* v___x_1664_; 
lean_dec_ref(v___x_1662_);
v_sz_1663_ = lean_array_size(v_snd_1658_);
v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_1663_, v___x_1661_, v_snd_1658_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
return v___x_1664_;
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_snd_1658_);
v_a_1665_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1662_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1662_);
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
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
v_a_1673_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1655_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1655_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___boxed(lean_object* v_elimInfo_1681_, lean_object* v_targets_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Meta_addImplicitTargets(v_elimInfo_1681_, v_targets_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec_ref(v_targets_1682_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(lean_object* v_mvarId_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_mvarId_1689_, v___y_1691_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___boxed(lean_object* v_mvarId_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(v_mvarId_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v_mvarId_1696_);
return v_res_1702_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(lean_object* v_00_u03b2_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_1704_, v_x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_){
_start:
{
uint8_t v_res_1710_; lean_object* v_r_1711_; 
v_res_1710_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(v_00_u03b2_1707_, v_x_1708_, v_x_1709_);
lean_dec(v_x_1709_);
v_r_1711_ = lean_box(v_res_1710_);
return v_r_1711_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1712_, lean_object* v_x_1713_, size_t v_x_1714_, lean_object* v_x_1715_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1713_, v_x_1714_, v_x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
size_t v_x_3700__boxed_1721_; uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_x_3700__boxed_1721_ = lean_unbox_usize(v_x_1719_);
lean_dec(v_x_1719_);
v_res_1722_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(v_00_u03b2_1717_, v_x_1718_, v_x_3700__boxed_1721_, v_x_1720_);
lean_dec(v_x_1720_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1724_, lean_object* v_keys_1725_, lean_object* v_vals_1726_, lean_object* v_heq_1727_, lean_object* v_i_1728_, lean_object* v_k_1729_){
_start:
{
uint8_t v___x_1730_; 
v___x_1730_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1725_, v_i_1728_, v_k_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1731_, lean_object* v_keys_1732_, lean_object* v_vals_1733_, lean_object* v_heq_1734_, lean_object* v_i_1735_, lean_object* v_k_1736_){
_start:
{
uint8_t v_res_1737_; lean_object* v_r_1738_; 
v_res_1737_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1731_, v_keys_1732_, v_vals_1733_, v_heq_1734_, v_i_1735_, v_k_1736_);
lean_dec(v_k_1736_);
lean_dec_ref(v_vals_1733_);
lean_dec_ref(v_keys_1732_);
v_r_1738_ = lean_box(v_res_1737_);
return v_r_1738_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
if (lean_obj_tag(v_x_1749_) == 0)
{
lean_dec(v_x_1747_);
return v_x_1748_;
}
else
{
lean_object* v_head_1750_; lean_object* v_tail_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1762_; 
v_head_1750_ = lean_ctor_get(v_x_1749_, 0);
v_tail_1751_ = lean_ctor_get(v_x_1749_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_x_1749_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1753_ = v_x_1749_;
v_isShared_1754_ = v_isSharedCheck_1762_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_tail_1751_);
lean_inc(v_head_1750_);
lean_dec(v_x_1749_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1762_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
lean_inc(v_x_1747_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 5);
lean_ctor_set(v___x_1753_, 1, v_x_1747_);
lean_ctor_set(v___x_1753_, 0, v_x_1748_);
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_x_1748_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_x_1747_);
v___x_1756_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = l_Lean_Name_reprPrec(v_head_1750_, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1756_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v_x_1748_ = v___x_1759_;
v_x_1749_ = v_tail_1751_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
if (lean_obj_tag(v_x_1765_) == 0)
{
lean_dec(v_x_1763_);
return v_x_1764_;
}
else
{
lean_object* v_head_1766_; lean_object* v_tail_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1778_; 
v_head_1766_ = lean_ctor_get(v_x_1765_, 0);
v_tail_1767_ = lean_ctor_get(v_x_1765_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_x_1765_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1769_ = v_x_1765_;
v_isShared_1770_ = v_isSharedCheck_1778_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_tail_1767_);
lean_inc(v_head_1766_);
lean_dec(v_x_1765_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1778_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
lean_inc(v_x_1763_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set_tag(v___x_1769_, 5);
lean_ctor_set(v___x_1769_, 1, v_x_1763_);
lean_ctor_set(v___x_1769_, 0, v_x_1764_);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_x_1764_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_x_1763_);
v___x_1772_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = l_Lean_Name_reprPrec(v_head_1766_, v___x_1773_);
v___x_1775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1772_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(v_x_1763_, v___x_1775_, v_tail_1767_);
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = l_Lean_Name_reprPrec(v___y_1779_, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(lean_object* v_x_1782_, lean_object* v_x_1783_){
_start:
{
if (lean_obj_tag(v_x_1782_) == 0)
{
lean_object* v___x_1784_; 
lean_dec(v_x_1783_);
v___x_1784_ = lean_box(0);
return v___x_1784_;
}
else
{
lean_object* v_tail_1785_; 
v_tail_1785_ = lean_ctor_get(v_x_1782_, 1);
if (lean_obj_tag(v_tail_1785_) == 0)
{
lean_object* v_head_1786_; lean_object* v___x_1787_; 
lean_dec(v_x_1783_);
v_head_1786_ = lean_ctor_get(v_x_1782_, 0);
lean_inc(v_head_1786_);
lean_dec_ref(v_x_1782_);
v___x_1787_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_1786_);
return v___x_1787_;
}
else
{
lean_object* v_head_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_inc(v_tail_1785_);
v_head_1788_ = lean_ctor_get(v_x_1782_, 0);
lean_inc(v_head_1788_);
lean_dec_ref(v_x_1782_);
v___x_1789_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_1788_);
v___x_1790_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(v_x_1783_, v___x_1789_, v_tail_1785_);
return v___x_1790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(lean_object* v_xs_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1792_ = lean_array_get_size(v_xs_1791_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_nat_dec_eq(v___x_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1795_ = lean_array_to_list(v_xs_1791_);
v___x_1796_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_1797_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(v___x_1795_, v___x_1796_);
v___x_1798_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4);
v___x_1799_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5));
v___x_1800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___x_1797_);
v___x_1801_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_1802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1798_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Std_Format_fill(v___x_1803_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; 
lean_dec_ref(v_xs_1791_);
v___x_1805_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8));
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg(lean_object* v_x_1820_){
_start:
{
uint8_t v_induction_1821_; lean_object* v_typeNames_1822_; lean_object* v_elimName_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v_induction_1821_ = lean_ctor_get_uint8(v_x_1820_, sizeof(void*)*2);
v_typeNames_1822_ = lean_ctor_get(v_x_1820_, 0);
lean_inc_ref(v_typeNames_1822_);
v_elimName_1823_ = lean_ctor_get(v_x_1820_, 1);
lean_inc(v_elimName_1823_);
lean_dec_ref(v_x_1820_);
v___x_1824_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5));
v___x_1825_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2));
v___x_1826_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12);
v___x_1827_ = lean_unsigned_to_nat(0u);
v___x_1828_ = l_Bool_repr___redArg(v_induction_1821_);
v___x_1829_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1826_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = 0;
v___x_1831_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*1, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1825_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9));
v___x_1834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = lean_box(1);
v___x_1836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4));
v___x_1838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v___x_1824_);
v___x_1840_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_typeNames_1822_);
v___x_1841_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1826_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set_uint8(v___x_1842_, sizeof(void*)*1, v___x_1830_);
v___x_1843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1839_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v___x_1833_);
v___x_1845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___x_1835_);
v___x_1846_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6));
v___x_1847_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v___x_1824_);
v___x_1849_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4);
v___x_1850_ = l_Lean_Name_reprPrec(v_elimName_1823_, v___x_1827_);
v___x_1851_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set_uint8(v___x_1852_, sizeof(void*)*1, v___x_1830_);
v___x_1853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1848_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_1855_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_1856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v___x_1853_);
v___x_1857_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_1858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1854_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*1, v___x_1830_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr(lean_object* v_x_1861_, lean_object* v_prec_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Meta_instReprCustomEliminator_repr___redArg(v_x_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___boxed(lean_object* v_x_1864_, lean_object* v_prec_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Meta_instReprCustomEliminator_repr(v_x_1864_, v_prec_1865_);
lean_dec(v_prec_1865_);
return v_res_1866_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_box(0);
v___x_1870_ = lean_unsigned_to_nat(16u);
v___x_1871_ = lean_mk_array(v___x_1870_, v___x_1869_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0);
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v___x_1872_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2(void){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; 
v___x_1878_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3);
v___x_1879_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1);
v___x_1880_ = 1;
v___x_1881_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v___x_1878_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*2, v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default(void){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4);
return v___x_1882_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators(void){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0(lean_object* v_f_1884_, lean_object* v_x1_1885_, lean_object* v_x2_1886_, lean_object* v_x3_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_apply_3(v_f_1884_, v_x1_1885_, v_x2_1886_, v_x3_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(lean_object* v_f_1889_, lean_object* v_keys_1890_, lean_object* v_vals_1891_, lean_object* v_i_1892_, lean_object* v_acc_1893_){
_start:
{
lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = lean_array_get_size(v_keys_1890_);
v___x_1895_ = lean_nat_dec_lt(v_i_1892_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_dec(v_i_1892_);
lean_dec(v_f_1889_);
return v_acc_1893_;
}
else
{
lean_object* v_k_1896_; lean_object* v_v_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_k_1896_ = lean_array_fget_borrowed(v_keys_1890_, v_i_1892_);
v_v_1897_ = lean_array_fget_borrowed(v_vals_1891_, v_i_1892_);
lean_inc(v_f_1889_);
lean_inc(v_v_1897_);
lean_inc(v_k_1896_);
v___x_1898_ = lean_apply_3(v_f_1889_, v_acc_1893_, v_k_1896_, v_v_1897_);
v___x_1899_ = lean_unsigned_to_nat(1u);
v___x_1900_ = lean_nat_add(v_i_1892_, v___x_1899_);
lean_dec(v_i_1892_);
v_i_1892_ = v___x_1900_;
v_acc_1893_ = v___x_1898_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg___boxed(lean_object* v_f_1902_, lean_object* v_keys_1903_, lean_object* v_vals_1904_, lean_object* v_i_1905_, lean_object* v_acc_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_1902_, v_keys_1903_, v_vals_1904_, v_i_1905_, v_acc_1906_);
lean_dec_ref(v_vals_1904_);
lean_dec_ref(v_keys_1903_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_){
_start:
{
if (lean_obj_tag(v_x_1909_) == 0)
{
lean_object* v_es_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_es_1911_ = lean_ctor_get(v_x_1909_, 0);
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = lean_array_get_size(v_es_1911_);
v___x_1914_ = lean_nat_dec_lt(v___x_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_dec(v_f_1908_);
return v_x_1910_;
}
else
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_nat_dec_le(v___x_1913_, v___x_1913_);
if (v___x_1915_ == 0)
{
if (v___x_1914_ == 0)
{
lean_dec(v_f_1908_);
return v_x_1910_;
}
else
{
size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = ((size_t)0ULL);
v___x_1917_ = lean_usize_of_nat(v___x_1913_);
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1908_, v_es_1911_, v___x_1916_, v___x_1917_, v_x_1910_);
return v___x_1918_;
}
}
else
{
size_t v___x_1919_; size_t v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = ((size_t)0ULL);
v___x_1920_ = lean_usize_of_nat(v___x_1913_);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1908_, v_es_1911_, v___x_1919_, v___x_1920_, v_x_1910_);
return v___x_1921_;
}
}
}
else
{
lean_object* v_ks_1922_; lean_object* v_vs_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_ks_1922_ = lean_ctor_get(v_x_1909_, 0);
v_vs_1923_ = lean_ctor_get(v_x_1909_, 1);
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_1908_, v_ks_1922_, v_vs_1923_, v___x_1924_, v_x_1910_);
return v___x_1925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(lean_object* v_f_1926_, lean_object* v_as_1927_, size_t v_i_1928_, size_t v_stop_1929_, lean_object* v_b_1930_){
_start:
{
lean_object* v___y_1932_; uint8_t v___x_1936_; 
v___x_1936_ = lean_usize_dec_eq(v_i_1928_, v_stop_1929_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_array_uget_borrowed(v_as_1927_, v_i_1928_);
switch(lean_obj_tag(v___x_1937_))
{
case 0:
{
lean_object* v_key_1938_; lean_object* v_val_1939_; lean_object* v___x_1940_; 
v_key_1938_ = lean_ctor_get(v___x_1937_, 0);
v_val_1939_ = lean_ctor_get(v___x_1937_, 1);
lean_inc(v_f_1926_);
lean_inc(v_val_1939_);
lean_inc(v_key_1938_);
v___x_1940_ = lean_apply_3(v_f_1926_, v_b_1930_, v_key_1938_, v_val_1939_);
v___y_1932_ = v___x_1940_;
goto v___jp_1931_;
}
case 1:
{
lean_object* v_node_1941_; lean_object* v___x_1942_; 
v_node_1941_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_f_1926_);
v___x_1942_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_1926_, v_node_1941_, v_b_1930_);
v___y_1932_ = v___x_1942_;
goto v___jp_1931_;
}
default: 
{
v___y_1932_ = v_b_1930_;
goto v___jp_1931_;
}
}
}
else
{
lean_dec(v_f_1926_);
return v_b_1930_;
}
v___jp_1931_:
{
size_t v___x_1933_; size_t v___x_1934_; 
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = lean_usize_add(v_i_1928_, v___x_1933_);
v_i_1928_ = v___x_1934_;
v_b_1930_ = v___y_1932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(lean_object* v_f_1943_, lean_object* v_as_1944_, lean_object* v_i_1945_, lean_object* v_stop_1946_, lean_object* v_b_1947_){
_start:
{
size_t v_i_boxed_1948_; size_t v_stop_boxed_1949_; lean_object* v_res_1950_; 
v_i_boxed_1948_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_stop_boxed_1949_ = lean_unbox_usize(v_stop_1946_);
lean_dec(v_stop_1946_);
v_res_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1943_, v_as_1944_, v_i_boxed_1948_, v_stop_boxed_1949_, v_b_1947_);
lean_dec_ref(v_as_1944_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_1951_, v_x_1952_, v_x_1953_);
lean_dec_ref(v_x_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_map_1955_, lean_object* v_f_1956_, lean_object* v_init_1957_){
_start:
{
lean_object* v___f_1958_; lean_object* v___x_1959_; 
v___f_1958_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1958_, 0, v_f_1956_);
v___x_1959_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v___f_1958_, v_map_1955_, v_init_1957_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_map_1960_, lean_object* v_f_1961_, lean_object* v_init_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_1960_, v_f_1961_, v_init_1962_);
lean_dec_ref(v_map_1960_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1964_, lean_object* v_x_1965_, lean_object* v_x_1966_){
_start:
{
if (lean_obj_tag(v_x_1966_) == 0)
{
lean_dec(v_f_1964_);
return v_x_1965_;
}
else
{
lean_object* v_key_1967_; lean_object* v_value_1968_; lean_object* v_tail_1969_; lean_object* v___x_1970_; 
v_key_1967_ = lean_ctor_get(v_x_1966_, 0);
lean_inc(v_key_1967_);
v_value_1968_ = lean_ctor_get(v_x_1966_, 1);
lean_inc(v_value_1968_);
v_tail_1969_ = lean_ctor_get(v_x_1966_, 2);
lean_inc(v_tail_1969_);
lean_dec_ref(v_x_1966_);
lean_inc(v_f_1964_);
v___x_1970_ = lean_apply_3(v_f_1964_, v_x_1965_, v_key_1967_, v_value_1968_);
v_x_1965_ = v___x_1970_;
v_x_1966_ = v_tail_1969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(lean_object* v_f_1972_, lean_object* v_as_1973_, size_t v_i_1974_, size_t v_stop_1975_, lean_object* v_b_1976_){
_start:
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_usize_dec_eq(v_i_1974_, v_stop_1975_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; size_t v___x_1980_; size_t v___x_1981_; 
v___x_1978_ = lean_array_uget_borrowed(v_as_1973_, v_i_1974_);
lean_inc(v___x_1978_);
lean_inc(v_f_1972_);
v___x_1979_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_1972_, v_b_1976_, v___x_1978_);
v___x_1980_ = ((size_t)1ULL);
v___x_1981_ = lean_usize_add(v_i_1974_, v___x_1980_);
v_i_1974_ = v___x_1981_;
v_b_1976_ = v___x_1979_;
goto _start;
}
else
{
lean_dec(v_f_1972_);
return v_b_1976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_f_1983_, lean_object* v_as_1984_, lean_object* v_i_1985_, lean_object* v_stop_1986_, lean_object* v_b_1987_){
_start:
{
size_t v_i_boxed_1988_; size_t v_stop_boxed_1989_; lean_object* v_res_1990_; 
v_i_boxed_1988_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_stop_boxed_1989_ = lean_unbox_usize(v_stop_1986_);
lean_dec(v_stop_1986_);
v_res_1990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1983_, v_as_1984_, v_i_boxed_1988_, v_stop_boxed_1989_, v_b_1987_);
lean_dec_ref(v_as_1984_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(lean_object* v_f_1991_, lean_object* v_init_1992_, lean_object* v_m_1993_){
_start:
{
lean_object* v_map_u2081_1994_; lean_object* v_map_u2082_1995_; lean_object* v_buckets_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v_map_u2081_1994_ = lean_ctor_get(v_m_1993_, 0);
v_map_u2082_1995_ = lean_ctor_get(v_m_1993_, 1);
v_buckets_1996_ = lean_ctor_get(v_map_u2081_1994_, 1);
v___x_1997_ = lean_unsigned_to_nat(0u);
v___x_1998_ = lean_array_get_size(v_buckets_1996_);
v___x_1999_ = lean_nat_dec_lt(v___x_1997_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1995_, v_f_1991_, v_init_1992_);
return v___x_2000_;
}
else
{
uint8_t v___x_2001_; 
v___x_2001_ = lean_nat_dec_le(v___x_1998_, v___x_1998_);
if (v___x_2001_ == 0)
{
if (v___x_1999_ == 0)
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1995_, v_f_1991_, v_init_1992_);
return v___x_2002_;
}
else
{
size_t v___x_2003_; size_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2003_ = ((size_t)0ULL);
v___x_2004_ = lean_usize_of_nat(v___x_1998_);
lean_inc(v_f_1991_);
v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1991_, v_buckets_1996_, v___x_2003_, v___x_2004_, v_init_1992_);
v___x_2006_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1995_, v_f_1991_, v___x_2005_);
return v___x_2006_;
}
}
else
{
size_t v___x_2007_; size_t v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2007_ = ((size_t)0ULL);
v___x_2008_ = lean_usize_of_nat(v___x_1998_);
lean_inc(v_f_1991_);
v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1991_, v_buckets_1996_, v___x_2007_, v___x_2008_, v_init_1992_);
v___x_2010_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1995_, v_f_1991_, v___x_2009_);
return v___x_2010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg___boxed(lean_object* v_f_2011_, lean_object* v_init_2012_, lean_object* v_m_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_2011_, v_init_2012_, v_m_2013_);
lean_dec_ref(v_m_2013_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0(lean_object* v_es_2015_, lean_object* v_a_2016_, lean_object* v_b_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v_a_2016_);
lean_ctor_set(v___x_2018_, 1, v_b_2017_);
v___x_2019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v_es_2015_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(lean_object* v_m_2021_){
_start:
{
lean_object* v___f_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___f_2022_ = ((lean_object*)(l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0));
v___x_2023_ = lean_box(0);
v___x_2024_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v___f_2022_, v___x_2023_, v_m_2021_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___boxed(lean_object* v_m_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_m_2025_);
lean_dec_ref(v_m_2025_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
if (lean_obj_tag(v_x_2029_) == 0)
{
lean_dec(v_x_2027_);
return v_x_2028_;
}
else
{
lean_object* v_head_2030_; lean_object* v_tail_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2040_; 
v_head_2030_ = lean_ctor_get(v_x_2029_, 0);
v_tail_2031_ = lean_ctor_get(v_x_2029_, 1);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_x_2029_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2033_ = v_x_2029_;
v_isShared_2034_ = v_isSharedCheck_2040_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_tail_2031_);
lean_inc(v_head_2030_);
lean_dec(v_x_2029_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2040_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
lean_inc(v_x_2027_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 5);
lean_ctor_set(v___x_2033_, 1, v_x_2027_);
lean_ctor_set(v___x_2033_, 0, v_x_2028_);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_x_2028_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_x_2027_);
v___x_2036_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_ctor_set(v___x_2037_, 1, v_head_2030_);
v_x_2028_ = v___x_2037_;
v_x_2029_ = v_tail_2031_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(lean_object* v_x_2041_, lean_object* v_x_2042_){
_start:
{
if (lean_obj_tag(v_x_2041_) == 0)
{
lean_object* v___x_2043_; 
lean_dec(v_x_2042_);
v___x_2043_ = lean_box(0);
return v___x_2043_;
}
else
{
lean_object* v_tail_2044_; 
v_tail_2044_ = lean_ctor_get(v_x_2041_, 1);
if (lean_obj_tag(v_tail_2044_) == 0)
{
lean_object* v_head_2045_; 
lean_dec(v_x_2042_);
v_head_2045_ = lean_ctor_get(v_x_2041_, 0);
lean_inc(v_head_2045_);
lean_dec_ref(v_x_2041_);
return v_head_2045_;
}
else
{
lean_object* v_head_2046_; lean_object* v___x_2047_; 
lean_inc(v_tail_2044_);
v_head_2046_ = lean_ctor_get(v_x_2041_, 0);
lean_inc(v_head_2046_);
lean_dec_ref(v_x_2041_);
v___x_2047_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(v_x_2042_, v_head_2046_, v_tail_2044_);
return v___x_2047_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0));
v___x_2051_ = lean_string_length(v___x_2050_);
return v___x_2051_;
}
}
static lean_object* _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2);
v___x_2053_ = lean_nat_to_int(v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(lean_object* v_x_2058_){
_start:
{
lean_object* v_fst_2059_; lean_object* v_snd_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2083_; 
v_fst_2059_ = lean_ctor_get(v_x_2058_, 0);
v_snd_2060_ = lean_ctor_get(v_x_2058_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_x_2058_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2062_ = v_x_2058_;
v_isShared_2063_ = v_isSharedCheck_2083_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_snd_2060_);
lean_inc(v_fst_2059_);
lean_dec(v_x_2058_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2083_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2064_ = lean_unbox(v_fst_2059_);
lean_dec(v_fst_2059_);
v___x_2065_ = l_Bool_repr___redArg(v___x_2064_);
v___x_2066_ = lean_box(0);
if (v_isShared_2063_ == 0)
{
lean_ctor_set_tag(v___x_2062_, 1);
lean_ctor_set(v___x_2062_, 1, v___x_2066_);
lean_ctor_set(v___x_2062_, 0, v___x_2065_);
v___x_2068_ = v___x_2062_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2069_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_snd_2060_);
v___x_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___x_2068_);
v___x_2071_ = l_List_reverse___redArg(v___x_2070_);
v___x_2072_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2073_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(v___x_2071_, v___x_2072_);
v___x_2074_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3);
v___x_2075_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4));
v___x_2076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___x_2073_);
v___x_2077_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5));
v___x_2078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2076_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2074_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = 0;
v___x_2081_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*1, v___x_2080_);
return v___x_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(lean_object* v_x_2084_){
_start:
{
lean_object* v_fst_2085_; lean_object* v_snd_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2109_; 
v_fst_2085_ = lean_ctor_get(v_x_2084_, 0);
v_snd_2086_ = lean_ctor_get(v_x_2084_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_x_2084_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2088_ = v_x_2084_;
v_isShared_2089_ = v_isSharedCheck_2109_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_snd_2086_);
lean_inc(v_fst_2085_);
lean_dec(v_x_2084_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2109_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(v_fst_2085_);
v___x_2092_ = lean_box(0);
if (v_isShared_2089_ == 0)
{
lean_ctor_set_tag(v___x_2088_, 1);
lean_ctor_set(v___x_2088_, 1, v___x_2092_);
lean_ctor_set(v___x_2088_, 0, v___x_2091_);
v___x_2094_ = v___x_2088_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; 
v___x_2095_ = l_Lean_Name_reprPrec(v_snd_2086_, v___x_2090_);
v___x_2096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
lean_ctor_set(v___x_2096_, 1, v___x_2094_);
v___x_2097_ = l_List_reverse___redArg(v___x_2096_);
v___x_2098_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2099_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(v___x_2097_, v___x_2098_);
v___x_2100_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3);
v___x_2101_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4));
v___x_2102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v___x_2099_);
v___x_2103_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5));
v___x_2104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2100_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = 0;
v___x_2107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set_uint8(v___x_2107_, sizeof(void*)*1, v___x_2106_);
return v___x_2107_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(lean_object* v_x_2110_, lean_object* v_x_2111_, lean_object* v_x_2112_){
_start:
{
if (lean_obj_tag(v_x_2112_) == 0)
{
lean_dec(v_x_2110_);
return v_x_2111_;
}
else
{
lean_object* v_head_2113_; lean_object* v_tail_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2124_; 
v_head_2113_ = lean_ctor_get(v_x_2112_, 0);
v_tail_2114_ = lean_ctor_get(v_x_2112_, 1);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_x_2112_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2116_ = v_x_2112_;
v_isShared_2117_ = v_isSharedCheck_2124_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_tail_2114_);
lean_inc(v_head_2113_);
lean_dec(v_x_2112_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2124_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
lean_inc(v_x_2110_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set_tag(v___x_2116_, 5);
lean_ctor_set(v___x_2116_, 1, v_x_2110_);
lean_ctor_set(v___x_2116_, 0, v_x_2111_);
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_x_2111_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_x_2110_);
v___x_2119_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2113_);
v___x_2121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v_x_2111_ = v___x_2121_;
v_x_2112_ = v_tail_2114_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(lean_object* v_x_2125_, lean_object* v_x_2126_, lean_object* v_x_2127_){
_start:
{
if (lean_obj_tag(v_x_2127_) == 0)
{
lean_dec(v_x_2125_);
return v_x_2126_;
}
else
{
lean_object* v_head_2128_; lean_object* v_tail_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2139_; 
v_head_2128_ = lean_ctor_get(v_x_2127_, 0);
v_tail_2129_ = lean_ctor_get(v_x_2127_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_x_2127_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2131_ = v_x_2127_;
v_isShared_2132_ = v_isSharedCheck_2139_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_tail_2129_);
lean_inc(v_head_2128_);
lean_dec(v_x_2127_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2139_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
lean_inc(v_x_2125_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 5);
lean_ctor_set(v___x_2131_, 1, v_x_2125_);
lean_ctor_set(v___x_2131_, 0, v_x_2126_);
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_x_2126_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_x_2125_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2128_);
v___x_2136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(v_x_2125_, v___x_2136_, v_tail_2129_);
return v___x_2137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(lean_object* v_x_2140_, lean_object* v_x_2141_){
_start:
{
if (lean_obj_tag(v_x_2140_) == 0)
{
lean_object* v___x_2142_; 
lean_dec(v_x_2141_);
v___x_2142_ = lean_box(0);
return v___x_2142_;
}
else
{
lean_object* v_tail_2143_; 
v_tail_2143_ = lean_ctor_get(v_x_2140_, 1);
if (lean_obj_tag(v_tail_2143_) == 0)
{
lean_object* v_head_2144_; lean_object* v___x_2145_; 
lean_dec(v_x_2141_);
v_head_2144_ = lean_ctor_get(v_x_2140_, 0);
lean_inc(v_head_2144_);
lean_dec_ref(v_x_2140_);
v___x_2145_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2144_);
return v___x_2145_;
}
else
{
lean_object* v_head_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_inc(v_tail_2143_);
v_head_2146_ = lean_ctor_get(v_x_2140_, 0);
lean_inc(v_head_2146_);
lean_dec_ref(v_x_2140_);
v___x_2147_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2146_);
v___x_2148_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(v_x_2141_, v___x_2147_, v_tail_2143_);
return v___x_2148_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2));
v___x_2154_ = lean_string_length(v___x_2153_);
return v___x_2154_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3, &l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3_once, _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3);
v___x_2156_ = lean_nat_to_int(v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(lean_object* v_a_2159_){
_start:
{
if (lean_obj_tag(v_a_2159_) == 0)
{
lean_object* v___x_2160_; 
v___x_2160_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1));
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2161_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2162_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(v_a_2159_, v___x_2161_);
v___x_2163_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4, &l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4);
v___x_2164_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5));
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v___x_2162_);
v___x_2166_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_2167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2163_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = 0;
v___x_2170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*1, v___x_2169_);
return v___x_2170_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_unsigned_to_nat(7u);
v___x_2181_ = lean_nat_to_int(v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg(lean_object* v_x_2185_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2186_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3));
v___x_2187_ = lean_obj_once(&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4, &l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4);
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_x_2185_);
v___x_2190_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v___x_2189_);
v___x_2191_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6));
v___x_2192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = l_Repr_addAppParen(v___x_2192_, v___x_2188_);
v___x_2194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2187_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = 0;
v___x_2196_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set_uint8(v___x_2196_, sizeof(void*)*1, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2186_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_2199_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_2200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v___x_2197_);
v___x_2201_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_2202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2198_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1, v___x_2195_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___boxed(lean_object* v_x_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_2205_);
lean_dec_ref(v_x_2205_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr(lean_object* v_x_2207_, lean_object* v_prec_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___boxed(lean_object* v_x_2210_, lean_object* v_prec_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_Meta_instReprCustomEliminators_repr(v_x_2210_, v_prec_2211_);
lean_dec(v_prec_2211_);
lean_dec_ref(v_x_2210_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(lean_object* v_00_u03b2_2213_, lean_object* v_m_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_m_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___boxed(lean_object* v_00_u03b2_2216_, lean_object* v_m_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(v_00_u03b2_2216_, v_m_2217_);
lean_dec_ref(v_m_2217_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(lean_object* v_a_2219_, lean_object* v_n_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v_a_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___boxed(lean_object* v_a_2222_, lean_object* v_n_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(v_a_2222_, v_n_2223_);
lean_dec(v_n_2223_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(lean_object* v_00_u03b2_2225_, lean_object* v_00_u03c3_2226_, lean_object* v_f_2227_, lean_object* v_init_2228_, lean_object* v_m_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_2227_, v_init_2228_, v_m_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2231_, lean_object* v_00_u03c3_2232_, lean_object* v_f_2233_, lean_object* v_init_2234_, lean_object* v_m_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(v_00_u03b2_2231_, v_00_u03c3_2232_, v_f_2233_, v_init_2234_, v_m_2235_);
lean_dec_ref(v_m_2235_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(lean_object* v_x_2237_, lean_object* v_x_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_x_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___boxed(lean_object* v_x_2240_, lean_object* v_x_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(v_x_2240_, v_x_2241_);
lean_dec(v_x_2241_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2243_, lean_object* v_00_u03c3_2244_, lean_object* v_f_2245_, lean_object* v_x_2246_, lean_object* v_x_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_2245_, v_x_2246_, v_x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_2249_, lean_object* v_00_u03b2_2250_, lean_object* v_map_2251_, lean_object* v_f_2252_, lean_object* v_init_2253_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_2251_, v_f_2252_, v_init_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_2255_, lean_object* v_00_u03b2_2256_, lean_object* v_map_2257_, lean_object* v_f_2258_, lean_object* v_init_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(v_00_u03c3_2255_, v_00_u03b2_2256_, v_map_2257_, v_f_2258_, v_init_2259_);
lean_dec_ref(v_map_2257_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2261_, lean_object* v_00_u03c3_2262_, lean_object* v_f_2263_, lean_object* v_as_2264_, size_t v_i_2265_, size_t v_stop_2266_, lean_object* v_b_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_2263_, v_as_2264_, v_i_2265_, v_stop_2266_, v_b_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2269_, lean_object* v_00_u03c3_2270_, lean_object* v_f_2271_, lean_object* v_as_2272_, lean_object* v_i_2273_, lean_object* v_stop_2274_, lean_object* v_b_2275_){
_start:
{
size_t v_i_boxed_2276_; size_t v_stop_boxed_2277_; lean_object* v_res_2278_; 
v_i_boxed_2276_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_stop_boxed_2277_ = lean_unbox_usize(v_stop_2274_);
lean_dec(v_stop_2274_);
v_res_2278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(v_00_u03b2_2269_, v_00_u03c3_2270_, v_f_2271_, v_as_2272_, v_i_boxed_2276_, v_stop_boxed_2277_, v_b_2275_);
lean_dec_ref(v_as_2272_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(lean_object* v_x_2279_, lean_object* v_x_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(v_x_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___boxed(lean_object* v_x_2282_, lean_object* v_x_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(v_x_2282_, v_x_2283_);
lean_dec(v_x_2283_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_map_2285_, lean_object* v_f_2286_, lean_object* v_init_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2286_, v_map_2285_, v_init_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_map_2289_, lean_object* v_f_2290_, lean_object* v_init_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(v_map_2289_, v_f_2290_, v_init_2291_);
lean_dec_ref(v_map_2289_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03c3_2293_, lean_object* v_00_u03b2_2294_, lean_object* v_map_2295_, lean_object* v_f_2296_, lean_object* v_init_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2296_, v_map_2295_, v_init_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03c3_2299_, lean_object* v_00_u03b2_2300_, lean_object* v_map_2301_, lean_object* v_f_2302_, lean_object* v_init_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(v_00_u03c3_2299_, v_00_u03b2_2300_, v_map_2301_, v_f_2302_, v_init_2303_);
lean_dec_ref(v_map_2301_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_2305_, lean_object* v_00_u03b1_2306_, lean_object* v_00_u03b2_2307_, lean_object* v_f_2308_, lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2308_, v_x_2309_, v_x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2312_, lean_object* v_00_u03b1_2313_, lean_object* v_00_u03b2_2314_, lean_object* v_f_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(v_00_u03c3_2312_, v_00_u03b1_2313_, v_00_u03b2_2314_, v_f_2315_, v_x_2316_, v_x_2317_);
lean_dec_ref(v_x_2316_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(lean_object* v_00_u03b1_2319_, lean_object* v_00_u03b2_2320_, lean_object* v_00_u03c3_2321_, lean_object* v_f_2322_, lean_object* v_as_2323_, size_t v_i_2324_, size_t v_stop_2325_, lean_object* v_b_2326_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_2322_, v_as_2323_, v_i_2324_, v_stop_2325_, v_b_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___boxed(lean_object* v_00_u03b1_2328_, lean_object* v_00_u03b2_2329_, lean_object* v_00_u03c3_2330_, lean_object* v_f_2331_, lean_object* v_as_2332_, lean_object* v_i_2333_, lean_object* v_stop_2334_, lean_object* v_b_2335_){
_start:
{
size_t v_i_boxed_2336_; size_t v_stop_boxed_2337_; lean_object* v_res_2338_; 
v_i_boxed_2336_ = lean_unbox_usize(v_i_2333_);
lean_dec(v_i_2333_);
v_stop_boxed_2337_ = lean_unbox_usize(v_stop_2334_);
lean_dec(v_stop_2334_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(v_00_u03b1_2328_, v_00_u03b2_2329_, v_00_u03c3_2330_, v_f_2331_, v_as_2332_, v_i_boxed_2336_, v_stop_boxed_2337_, v_b_2335_);
lean_dec_ref(v_as_2332_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(lean_object* v_00_u03c3_2339_, lean_object* v_00_u03b1_2340_, lean_object* v_00_u03b2_2341_, lean_object* v_f_2342_, lean_object* v_keys_2343_, lean_object* v_vals_2344_, lean_object* v_heq_2345_, lean_object* v_i_2346_, lean_object* v_acc_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_2342_, v_keys_2343_, v_vals_2344_, v_i_2346_, v_acc_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___boxed(lean_object* v_00_u03c3_2349_, lean_object* v_00_u03b1_2350_, lean_object* v_00_u03b2_2351_, lean_object* v_f_2352_, lean_object* v_keys_2353_, lean_object* v_vals_2354_, lean_object* v_heq_2355_, lean_object* v_i_2356_, lean_object* v_acc_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(v_00_u03c3_2349_, v_00_u03b1_2350_, v_00_u03b2_2351_, v_f_2352_, v_keys_2353_, v_vals_2354_, v_heq_2355_, v_i_2356_, v_acc_2357_);
lean_dec_ref(v_vals_2354_);
lean_dec_ref(v_keys_2353_);
return v_res_2358_;
}
}
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2361_; uint64_t v___x_2362_; 
v___x_2361_ = lean_unsigned_to_nat(1723u);
v___x_2362_ = lean_uint64_of_nat(v___x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(lean_object* v_as_2363_, size_t v_i_2364_, size_t v_stop_2365_, uint64_t v_b_2366_){
_start:
{
uint64_t v___y_2368_; uint8_t v___x_2373_; 
v___x_2373_ = lean_usize_dec_eq(v_i_2364_, v_stop_2365_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_array_uget_borrowed(v_as_2363_, v_i_2364_);
if (lean_obj_tag(v___x_2374_) == 0)
{
uint64_t v___x_2375_; 
v___x_2375_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0);
v___y_2368_ = v___x_2375_;
goto v___jp_2367_;
}
else
{
uint64_t v_hash_2376_; 
v_hash_2376_ = lean_ctor_get_uint64(v___x_2374_, sizeof(void*)*2);
v___y_2368_ = v_hash_2376_;
goto v___jp_2367_;
}
}
else
{
return v_b_2366_;
}
v___jp_2367_:
{
uint64_t v___x_2369_; size_t v___x_2370_; size_t v___x_2371_; 
v___x_2369_ = lean_uint64_mix_hash(v_b_2366_, v___y_2368_);
v___x_2370_ = ((size_t)1ULL);
v___x_2371_ = lean_usize_add(v_i_2364_, v___x_2370_);
v_i_2364_ = v___x_2371_;
v_b_2366_ = v___x_2369_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2377_, lean_object* v_i_2378_, lean_object* v_stop_2379_, lean_object* v_b_2380_){
_start:
{
size_t v_i_boxed_2381_; size_t v_stop_boxed_2382_; uint64_t v_b_boxed_2383_; uint64_t v_res_2384_; lean_object* v_r_2385_; 
v_i_boxed_2381_ = lean_unbox_usize(v_i_2378_);
lean_dec(v_i_2378_);
v_stop_boxed_2382_ = lean_unbox_usize(v_stop_2379_);
lean_dec(v_stop_2379_);
v_b_boxed_2383_ = lean_unbox_uint64(v_b_2380_);
lean_dec_ref(v_b_2380_);
v_res_2384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_as_2377_, v_i_boxed_2381_, v_stop_boxed_2382_, v_b_boxed_2383_);
lean_dec_ref(v_as_2377_);
v_r_2385_ = lean_box_uint64(v_res_2384_);
return v_r_2385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
if (lean_obj_tag(v_x_2387_) == 0)
{
return v_x_2386_;
}
else
{
lean_object* v_key_2388_; lean_object* v_value_2389_; lean_object* v_tail_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2434_; 
v_key_2388_ = lean_ctor_get(v_x_2387_, 0);
v_value_2389_ = lean_ctor_get(v_x_2387_, 1);
v_tail_2390_ = lean_ctor_get(v_x_2387_, 2);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_x_2387_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2392_ = v_x_2387_;
v_isShared_2393_ = v_isSharedCheck_2434_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_tail_2390_);
lean_inc(v_value_2389_);
lean_inc(v_key_2388_);
lean_dec(v_x_2387_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2434_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v_fst_2394_; lean_object* v_snd_2395_; lean_object* v___x_2396_; uint64_t v___y_2398_; uint64_t v___y_2399_; uint64_t v___y_2419_; uint8_t v___x_2431_; 
v_fst_2394_ = lean_ctor_get(v_key_2388_, 0);
v_snd_2395_ = lean_ctor_get(v_key_2388_, 1);
v___x_2396_ = lean_array_get_size(v_x_2386_);
v___x_2431_ = lean_unbox(v_fst_2394_);
if (v___x_2431_ == 0)
{
uint64_t v___x_2432_; 
v___x_2432_ = 13ULL;
v___y_2419_ = v___x_2432_;
goto v___jp_2418_;
}
else
{
uint64_t v___x_2433_; 
v___x_2433_ = 11ULL;
v___y_2419_ = v___x_2433_;
goto v___jp_2418_;
}
v___jp_2397_:
{
uint64_t v___x_2400_; uint64_t v___x_2401_; uint64_t v___x_2402_; uint64_t v_fold_2403_; uint64_t v___x_2404_; uint64_t v___x_2405_; uint64_t v___x_2406_; size_t v___x_2407_; size_t v___x_2408_; size_t v___x_2409_; size_t v___x_2410_; size_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2400_ = lean_uint64_mix_hash(v___y_2398_, v___y_2399_);
v___x_2401_ = 32ULL;
v___x_2402_ = lean_uint64_shift_right(v___x_2400_, v___x_2401_);
v_fold_2403_ = lean_uint64_xor(v___x_2400_, v___x_2402_);
v___x_2404_ = 16ULL;
v___x_2405_ = lean_uint64_shift_right(v_fold_2403_, v___x_2404_);
v___x_2406_ = lean_uint64_xor(v_fold_2403_, v___x_2405_);
v___x_2407_ = lean_uint64_to_usize(v___x_2406_);
v___x_2408_ = lean_usize_of_nat(v___x_2396_);
v___x_2409_ = ((size_t)1ULL);
v___x_2410_ = lean_usize_sub(v___x_2408_, v___x_2409_);
v___x_2411_ = lean_usize_land(v___x_2407_, v___x_2410_);
v___x_2412_ = lean_array_uget_borrowed(v_x_2386_, v___x_2411_);
lean_inc(v___x_2412_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 2, v___x_2412_);
v___x_2414_ = v___x_2392_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_key_2388_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_value_2389_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_array_uset(v_x_2386_, v___x_2411_, v___x_2414_);
v_x_2386_ = v___x_2415_;
v_x_2387_ = v_tail_2390_;
goto _start;
}
}
v___jp_2418_:
{
uint64_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2420_ = 7ULL;
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_array_get_size(v_snd_2395_);
v___x_2423_ = lean_nat_dec_lt(v___x_2421_, v___x_2422_);
if (v___x_2423_ == 0)
{
v___y_2398_ = v___y_2419_;
v___y_2399_ = v___x_2420_;
goto v___jp_2397_;
}
else
{
uint8_t v___x_2424_; 
v___x_2424_ = lean_nat_dec_le(v___x_2422_, v___x_2422_);
if (v___x_2424_ == 0)
{
if (v___x_2423_ == 0)
{
v___y_2398_ = v___y_2419_;
v___y_2399_ = v___x_2420_;
goto v___jp_2397_;
}
else
{
size_t v___x_2425_; size_t v___x_2426_; uint64_t v___x_2427_; 
v___x_2425_ = ((size_t)0ULL);
v___x_2426_ = lean_usize_of_nat(v___x_2422_);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2395_, v___x_2425_, v___x_2426_, v___x_2420_);
v___y_2398_ = v___y_2419_;
v___y_2399_ = v___x_2427_;
goto v___jp_2397_;
}
}
else
{
size_t v___x_2428_; size_t v___x_2429_; uint64_t v___x_2430_; 
v___x_2428_ = ((size_t)0ULL);
v___x_2429_ = lean_usize_of_nat(v___x_2422_);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2395_, v___x_2428_, v___x_2429_, v___x_2420_);
v___y_2398_ = v___y_2419_;
v___y_2399_ = v___x_2430_;
goto v___jp_2397_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_i_2435_, lean_object* v_source_2436_, lean_object* v_target_2437_){
_start:
{
lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2438_ = lean_array_get_size(v_source_2436_);
v___x_2439_ = lean_nat_dec_lt(v_i_2435_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_dec_ref(v_source_2436_);
lean_dec(v_i_2435_);
return v_target_2437_;
}
else
{
lean_object* v_es_2440_; lean_object* v___x_2441_; lean_object* v_source_2442_; lean_object* v_target_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_es_2440_ = lean_array_fget(v_source_2436_, v_i_2435_);
v___x_2441_ = lean_box(0);
v_source_2442_ = lean_array_fset(v_source_2436_, v_i_2435_, v___x_2441_);
v_target_2443_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(v_target_2437_, v_es_2440_);
v___x_2444_ = lean_unsigned_to_nat(1u);
v___x_2445_ = lean_nat_add(v_i_2435_, v___x_2444_);
lean_dec(v_i_2435_);
v_i_2435_ = v___x_2445_;
v_source_2436_ = v_source_2442_;
v_target_2437_ = v_target_2443_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_data_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v_nbuckets_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2448_ = lean_array_get_size(v_data_2447_);
v___x_2449_ = lean_unsigned_to_nat(2u);
v_nbuckets_2450_ = lean_nat_mul(v___x_2448_, v___x_2449_);
v___x_2451_ = lean_unsigned_to_nat(0u);
v___x_2452_ = lean_box(0);
v___x_2453_ = lean_mk_array(v_nbuckets_2450_, v___x_2452_);
v___x_2454_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(v___x_2451_, v_data_2447_, v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_xs_2455_, lean_object* v_ys_2456_, lean_object* v_x_2457_){
_start:
{
lean_object* v_zero_2458_; uint8_t v_isZero_2459_; 
v_zero_2458_ = lean_unsigned_to_nat(0u);
v_isZero_2459_ = lean_nat_dec_eq(v_x_2457_, v_zero_2458_);
if (v_isZero_2459_ == 1)
{
lean_dec(v_x_2457_);
return v_isZero_2459_;
}
else
{
lean_object* v_one_2460_; lean_object* v_n_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v_one_2460_ = lean_unsigned_to_nat(1u);
v_n_2461_ = lean_nat_sub(v_x_2457_, v_one_2460_);
lean_dec(v_x_2457_);
v___x_2462_ = lean_array_fget_borrowed(v_xs_2455_, v_n_2461_);
v___x_2463_ = lean_array_fget_borrowed(v_ys_2456_, v_n_2461_);
v___x_2464_ = lean_name_eq(v___x_2462_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_dec(v_n_2461_);
return v___x_2464_;
}
else
{
v_x_2457_ = v_n_2461_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_xs_2466_, lean_object* v_ys_2467_, lean_object* v_x_2468_){
_start:
{
uint8_t v_res_2469_; lean_object* v_r_2470_; 
v_res_2469_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_2466_, v_ys_2467_, v_x_2468_);
lean_dec_ref(v_ys_2467_);
lean_dec_ref(v_xs_2466_);
v_r_2470_ = lean_box(v_res_2469_);
return v_r_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(lean_object* v_a_2471_, lean_object* v_b_2472_, lean_object* v_x_2473_){
_start:
{
if (lean_obj_tag(v_x_2473_) == 0)
{
lean_dec(v_b_2472_);
lean_dec_ref(v_a_2471_);
return v_x_2473_;
}
else
{
lean_object* v_key_2474_; lean_object* v_value_2475_; lean_object* v_tail_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2498_; 
v_key_2474_ = lean_ctor_get(v_x_2473_, 0);
v_value_2475_ = lean_ctor_get(v_x_2473_, 1);
v_tail_2476_ = lean_ctor_get(v_x_2473_, 2);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_x_2473_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2478_ = v_x_2473_;
v_isShared_2479_ = v_isSharedCheck_2498_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_tail_2476_);
lean_inc(v_value_2475_);
lean_inc(v_key_2474_);
lean_dec(v_x_2473_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2498_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v_fst_2485_; lean_object* v_snd_2486_; lean_object* v_fst_2487_; lean_object* v_snd_2488_; uint8_t v___x_2495_; 
v_fst_2485_ = lean_ctor_get(v_key_2474_, 0);
v_snd_2486_ = lean_ctor_get(v_key_2474_, 1);
v_fst_2487_ = lean_ctor_get(v_a_2471_, 0);
v_snd_2488_ = lean_ctor_get(v_a_2471_, 1);
v___x_2495_ = lean_unbox(v_fst_2485_);
if (v___x_2495_ == 0)
{
uint8_t v___x_2496_; 
v___x_2496_ = lean_unbox(v_fst_2487_);
if (v___x_2496_ == 0)
{
goto v___jp_2489_;
}
else
{
goto v___jp_2480_;
}
}
else
{
uint8_t v___x_2497_; 
v___x_2497_ = lean_unbox(v_fst_2487_);
if (v___x_2497_ == 0)
{
goto v___jp_2480_;
}
else
{
goto v___jp_2489_;
}
}
v___jp_2480_:
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2471_, v_b_2472_, v_tail_2476_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 2, v___x_2481_);
v___x_2483_ = v___x_2478_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_key_2474_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_value_2475_);
lean_ctor_set(v_reuseFailAlloc_2484_, 2, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
v___jp_2489_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2490_ = lean_array_get_size(v_snd_2486_);
v___x_2491_ = lean_array_get_size(v_snd_2488_);
v___x_2492_ = lean_nat_dec_eq(v___x_2490_, v___x_2491_);
if (v___x_2492_ == 0)
{
goto v___jp_2480_;
}
else
{
uint8_t v___x_2493_; 
v___x_2493_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2486_, v_snd_2488_, v___x_2490_);
if (v___x_2493_ == 0)
{
goto v___jp_2480_;
}
else
{
lean_object* v___x_2494_; 
lean_del_object(v___x_2478_);
lean_dec(v_value_2475_);
lean_dec(v_key_2474_);
v___x_2494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2494_, 0, v_a_2471_);
lean_ctor_set(v___x_2494_, 1, v_b_2472_);
lean_ctor_set(v___x_2494_, 2, v_tail_2476_);
return v___x_2494_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(lean_object* v_a_2499_, lean_object* v_x_2500_){
_start:
{
if (lean_obj_tag(v_x_2500_) == 0)
{
uint8_t v___x_2501_; 
v___x_2501_ = 0;
return v___x_2501_;
}
else
{
lean_object* v_key_2502_; lean_object* v_tail_2503_; lean_object* v_fst_2504_; lean_object* v_snd_2505_; lean_object* v_fst_2506_; lean_object* v_snd_2507_; uint8_t v___x_2515_; 
v_key_2502_ = lean_ctor_get(v_x_2500_, 0);
v_tail_2503_ = lean_ctor_get(v_x_2500_, 2);
v_fst_2504_ = lean_ctor_get(v_key_2502_, 0);
v_snd_2505_ = lean_ctor_get(v_key_2502_, 1);
v_fst_2506_ = lean_ctor_get(v_a_2499_, 0);
v_snd_2507_ = lean_ctor_get(v_a_2499_, 1);
v___x_2515_ = lean_unbox(v_fst_2504_);
if (v___x_2515_ == 0)
{
uint8_t v___x_2516_; 
v___x_2516_ = lean_unbox(v_fst_2506_);
if (v___x_2516_ == 0)
{
goto v___jp_2508_;
}
else
{
v_x_2500_ = v_tail_2503_;
goto _start;
}
}
else
{
uint8_t v___x_2518_; 
v___x_2518_ = lean_unbox(v_fst_2506_);
if (v___x_2518_ == 0)
{
v_x_2500_ = v_tail_2503_;
goto _start;
}
else
{
goto v___jp_2508_;
}
}
v___jp_2508_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2509_ = lean_array_get_size(v_snd_2505_);
v___x_2510_ = lean_array_get_size(v_snd_2507_);
v___x_2511_ = lean_nat_dec_eq(v___x_2509_, v___x_2510_);
if (v___x_2511_ == 0)
{
v_x_2500_ = v_tail_2503_;
goto _start;
}
else
{
uint8_t v___x_2513_; 
v___x_2513_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2505_, v_snd_2507_, v___x_2509_);
if (v___x_2513_ == 0)
{
v_x_2500_ = v_tail_2503_;
goto _start;
}
else
{
return v___x_2513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_a_2520_, lean_object* v_x_2521_){
_start:
{
uint8_t v_res_2522_; lean_object* v_r_2523_; 
v_res_2522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2520_, v_x_2521_);
lean_dec(v_x_2521_);
lean_dec_ref(v_a_2520_);
v_r_2523_ = lean_box(v_res_2522_);
return v_r_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(lean_object* v_m_2524_, lean_object* v_a_2525_, lean_object* v_b_2526_){
_start:
{
lean_object* v_size_2527_; lean_object* v_buckets_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2592_; 
v_size_2527_ = lean_ctor_get(v_m_2524_, 0);
v_buckets_2528_ = lean_ctor_get(v_m_2524_, 1);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_m_2524_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2530_ = v_m_2524_;
v_isShared_2531_ = v_isSharedCheck_2592_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_buckets_2528_);
lean_inc(v_size_2527_);
lean_dec(v_m_2524_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2592_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v_fst_2532_; lean_object* v_snd_2533_; lean_object* v___x_2534_; uint64_t v___y_2536_; uint64_t v___y_2537_; uint64_t v___y_2577_; uint8_t v___x_2589_; 
v_fst_2532_ = lean_ctor_get(v_a_2525_, 0);
v_snd_2533_ = lean_ctor_get(v_a_2525_, 1);
v___x_2534_ = lean_array_get_size(v_buckets_2528_);
v___x_2589_ = lean_unbox(v_fst_2532_);
if (v___x_2589_ == 0)
{
uint64_t v___x_2590_; 
v___x_2590_ = 13ULL;
v___y_2577_ = v___x_2590_;
goto v___jp_2576_;
}
else
{
uint64_t v___x_2591_; 
v___x_2591_ = 11ULL;
v___y_2577_ = v___x_2591_;
goto v___jp_2576_;
}
v___jp_2535_:
{
uint64_t v___x_2538_; uint64_t v___x_2539_; uint64_t v___x_2540_; uint64_t v_fold_2541_; uint64_t v___x_2542_; uint64_t v___x_2543_; uint64_t v___x_2544_; size_t v___x_2545_; size_t v___x_2546_; size_t v___x_2547_; size_t v___x_2548_; size_t v___x_2549_; lean_object* v_bkt_2550_; uint8_t v___x_2551_; 
v___x_2538_ = lean_uint64_mix_hash(v___y_2536_, v___y_2537_);
v___x_2539_ = 32ULL;
v___x_2540_ = lean_uint64_shift_right(v___x_2538_, v___x_2539_);
v_fold_2541_ = lean_uint64_xor(v___x_2538_, v___x_2540_);
v___x_2542_ = 16ULL;
v___x_2543_ = lean_uint64_shift_right(v_fold_2541_, v___x_2542_);
v___x_2544_ = lean_uint64_xor(v_fold_2541_, v___x_2543_);
v___x_2545_ = lean_uint64_to_usize(v___x_2544_);
v___x_2546_ = lean_usize_of_nat(v___x_2534_);
v___x_2547_ = ((size_t)1ULL);
v___x_2548_ = lean_usize_sub(v___x_2546_, v___x_2547_);
v___x_2549_ = lean_usize_land(v___x_2545_, v___x_2548_);
v_bkt_2550_ = lean_array_uget_borrowed(v_buckets_2528_, v___x_2549_);
v___x_2551_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2525_, v_bkt_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v_size_x27_2553_; lean_object* v___x_2554_; lean_object* v_buckets_x27_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2552_ = lean_unsigned_to_nat(1u);
v_size_x27_2553_ = lean_nat_add(v_size_2527_, v___x_2552_);
lean_dec(v_size_2527_);
lean_inc(v_bkt_2550_);
v___x_2554_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2554_, 0, v_a_2525_);
lean_ctor_set(v___x_2554_, 1, v_b_2526_);
lean_ctor_set(v___x_2554_, 2, v_bkt_2550_);
v_buckets_x27_2555_ = lean_array_uset(v_buckets_2528_, v___x_2549_, v___x_2554_);
v___x_2556_ = lean_unsigned_to_nat(4u);
v___x_2557_ = lean_nat_mul(v_size_x27_2553_, v___x_2556_);
v___x_2558_ = lean_unsigned_to_nat(3u);
v___x_2559_ = lean_nat_div(v___x_2557_, v___x_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_array_get_size(v_buckets_x27_2555_);
v___x_2561_ = lean_nat_dec_le(v___x_2559_, v___x_2560_);
lean_dec(v___x_2559_);
if (v___x_2561_ == 0)
{
lean_object* v_val_2562_; lean_object* v___x_2564_; 
v_val_2562_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(v_buckets_x27_2555_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v_val_2562_);
lean_ctor_set(v___x_2530_, 0, v_size_x27_2553_);
v___x_2564_ = v___x_2530_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_size_x27_2553_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_val_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
else
{
lean_object* v___x_2567_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v_buckets_x27_2555_);
lean_ctor_set(v___x_2530_, 0, v_size_x27_2553_);
v___x_2567_ = v___x_2530_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_size_x27_2553_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_buckets_x27_2555_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
lean_object* v___x_2569_; lean_object* v_buckets_x27_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
lean_inc(v_bkt_2550_);
v___x_2569_ = lean_box(0);
v_buckets_x27_2570_ = lean_array_uset(v_buckets_2528_, v___x_2549_, v___x_2569_);
v___x_2571_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2525_, v_b_2526_, v_bkt_2550_);
v___x_2572_ = lean_array_uset(v_buckets_x27_2570_, v___x_2549_, v___x_2571_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v___x_2572_);
v___x_2574_ = v___x_2530_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_size_2527_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
v___jp_2576_:
{
uint64_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2578_ = 7ULL;
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = lean_array_get_size(v_snd_2533_);
v___x_2581_ = lean_nat_dec_lt(v___x_2579_, v___x_2580_);
if (v___x_2581_ == 0)
{
v___y_2536_ = v___y_2577_;
v___y_2537_ = v___x_2578_;
goto v___jp_2535_;
}
else
{
uint8_t v___x_2582_; 
v___x_2582_ = lean_nat_dec_le(v___x_2580_, v___x_2580_);
if (v___x_2582_ == 0)
{
if (v___x_2581_ == 0)
{
v___y_2536_ = v___y_2577_;
v___y_2537_ = v___x_2578_;
goto v___jp_2535_;
}
else
{
size_t v___x_2583_; size_t v___x_2584_; uint64_t v___x_2585_; 
v___x_2583_ = ((size_t)0ULL);
v___x_2584_ = lean_usize_of_nat(v___x_2580_);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2533_, v___x_2583_, v___x_2584_, v___x_2578_);
v___y_2536_ = v___y_2577_;
v___y_2537_ = v___x_2585_;
goto v___jp_2535_;
}
}
else
{
size_t v___x_2586_; size_t v___x_2587_; uint64_t v___x_2588_; 
v___x_2586_ = ((size_t)0ULL);
v___x_2587_ = lean_usize_of_nat(v___x_2580_);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2533_, v___x_2586_, v___x_2587_, v___x_2578_);
v___y_2536_ = v___y_2577_;
v___y_2537_ = v___x_2588_;
goto v___jp_2535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_2593_, lean_object* v_x_2594_, lean_object* v_x_2595_, lean_object* v_x_2596_){
_start:
{
lean_object* v_ks_2597_; lean_object* v_vs_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2637_; 
v_ks_2597_ = lean_ctor_get(v_x_2593_, 0);
v_vs_2598_ = lean_ctor_get(v_x_2593_, 1);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_x_2593_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2600_ = v_x_2593_;
v_isShared_2601_ = v_isSharedCheck_2637_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_vs_2598_);
lean_inc(v_ks_2597_);
lean_dec(v_x_2593_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2637_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = lean_array_get_size(v_ks_2597_);
v___x_2610_ = lean_nat_dec_lt(v_x_2594_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_del_object(v___x_2600_);
lean_dec(v_x_2594_);
v___x_2611_ = lean_array_push(v_ks_2597_, v_x_2595_);
v___x_2612_ = lean_array_push(v_vs_2598_, v_x_2596_);
v___x_2613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
return v___x_2613_;
}
else
{
lean_object* v_fst_2614_; lean_object* v_snd_2615_; lean_object* v_k_x27_2616_; lean_object* v_fst_2617_; lean_object* v_snd_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2636_; 
v_fst_2614_ = lean_ctor_get(v_x_2595_, 0);
v_snd_2615_ = lean_ctor_get(v_x_2595_, 1);
v_k_x27_2616_ = lean_array_fget(v_ks_2597_, v_x_2594_);
v_fst_2617_ = lean_ctor_get(v_k_x27_2616_, 0);
v_snd_2618_ = lean_ctor_get(v_k_x27_2616_, 1);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_k_x27_2616_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2620_ = v_k_x27_2616_;
v_isShared_2621_ = v_isSharedCheck_2636_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_snd_2618_);
lean_inc(v_fst_2617_);
lean_dec(v_k_x27_2616_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2636_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
uint8_t v___y_2623_; uint8_t v___x_2633_; 
v___x_2633_ = lean_unbox(v_fst_2614_);
if (v___x_2633_ == 0)
{
uint8_t v___x_2634_; 
v___x_2634_ = lean_unbox(v_fst_2617_);
lean_dec(v_fst_2617_);
if (v___x_2634_ == 0)
{
v___y_2623_ = v___x_2610_;
goto v___jp_2622_;
}
else
{
lean_del_object(v___x_2620_);
lean_dec(v_snd_2618_);
goto v___jp_2602_;
}
}
else
{
uint8_t v___x_2635_; 
v___x_2635_ = lean_unbox(v_fst_2617_);
lean_dec(v_fst_2617_);
v___y_2623_ = v___x_2635_;
goto v___jp_2622_;
}
v___jp_2622_:
{
if (v___y_2623_ == 0)
{
lean_del_object(v___x_2620_);
lean_dec(v_snd_2618_);
goto v___jp_2602_;
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v___x_2624_ = lean_array_get_size(v_snd_2615_);
v___x_2625_ = lean_array_get_size(v_snd_2618_);
v___x_2626_ = lean_nat_dec_eq(v___x_2624_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_del_object(v___x_2620_);
lean_dec(v_snd_2618_);
goto v___jp_2602_;
}
else
{
uint8_t v___x_2627_; 
v___x_2627_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2615_, v_snd_2618_, v___x_2624_);
lean_dec(v_snd_2618_);
if (v___x_2627_ == 0)
{
lean_del_object(v___x_2620_);
goto v___jp_2602_;
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
lean_del_object(v___x_2600_);
v___x_2628_ = lean_array_fset(v_ks_2597_, v_x_2594_, v_x_2595_);
v___x_2629_ = lean_array_fset(v_vs_2598_, v_x_2594_, v_x_2596_);
lean_dec(v_x_2594_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set_tag(v___x_2620_, 1);
lean_ctor_set(v___x_2620_, 1, v___x_2629_);
lean_ctor_set(v___x_2620_, 0, v___x_2628_);
v___x_2631_ = v___x_2620_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v___x_2629_);
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
}
}
}
v___jp_2602_:
{
lean_object* v___x_2604_; 
if (v_isShared_2601_ == 0)
{
v___x_2604_ = v___x_2600_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_ks_2597_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_vs_2598_);
v___x_2604_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_unsigned_to_nat(1u);
v___x_2606_ = lean_nat_add(v_x_2594_, v___x_2605_);
lean_dec(v_x_2594_);
v_x_2593_ = v___x_2604_;
v_x_2594_ = v___x_2606_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_2638_, lean_object* v_k_2639_, lean_object* v_v_2640_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_unsigned_to_nat(0u);
v___x_2642_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_n_2638_, v___x_2641_, v_k_2639_, v_v_2640_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2644_, size_t v_x_2645_, size_t v_x_2646_, lean_object* v_x_2647_, lean_object* v_x_2648_){
_start:
{
if (lean_obj_tag(v_x_2644_) == 0)
{
lean_object* v_es_2649_; size_t v___x_2650_; size_t v___x_2651_; size_t v___x_2652_; size_t v___x_2653_; lean_object* v_j_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v_es_2649_ = lean_ctor_get(v_x_2644_, 0);
v___x_2650_ = ((size_t)5ULL);
v___x_2651_ = ((size_t)1ULL);
v___x_2652_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_2653_ = lean_usize_land(v_x_2645_, v___x_2652_);
v_j_2654_ = lean_usize_to_nat(v___x_2653_);
v___x_2655_ = lean_array_get_size(v_es_2649_);
v___x_2656_ = lean_nat_dec_lt(v_j_2654_, v___x_2655_);
if (v___x_2656_ == 0)
{
lean_dec(v_j_2654_);
lean_dec(v_x_2648_);
lean_dec_ref(v_x_2647_);
return v_x_2644_;
}
else
{
lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2706_; 
lean_inc_ref(v_es_2649_);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; 
v_unused_2707_ = lean_ctor_get(v_x_2644_, 0);
lean_dec(v_unused_2707_);
v___x_2658_ = v_x_2644_;
v_isShared_2659_ = v_isSharedCheck_2706_;
goto v_resetjp_2657_;
}
else
{
lean_dec(v_x_2644_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2706_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v_v_2660_; lean_object* v___x_2661_; lean_object* v_xs_x27_2662_; lean_object* v___y_2664_; 
v_v_2660_ = lean_array_fget(v_es_2649_, v_j_2654_);
v___x_2661_ = lean_box(0);
v_xs_x27_2662_ = lean_array_fset(v_es_2649_, v_j_2654_, v___x_2661_);
switch(lean_obj_tag(v_v_2660_))
{
case 0:
{
lean_object* v_key_2669_; lean_object* v_val_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2693_; 
v_key_2669_ = lean_ctor_get(v_v_2660_, 0);
v_val_2670_ = lean_ctor_get(v_v_2660_, 1);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_v_2660_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2672_ = v_v_2660_;
v_isShared_2673_ = v_isSharedCheck_2693_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_val_2670_);
lean_inc(v_key_2669_);
lean_dec(v_v_2660_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2693_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v_fst_2677_; lean_object* v_snd_2678_; lean_object* v_fst_2679_; lean_object* v_snd_2680_; uint8_t v___y_2682_; uint8_t v___x_2690_; 
v_fst_2677_ = lean_ctor_get(v_x_2647_, 0);
v_snd_2678_ = lean_ctor_get(v_x_2647_, 1);
v_fst_2679_ = lean_ctor_get(v_key_2669_, 0);
v_snd_2680_ = lean_ctor_get(v_key_2669_, 1);
v___x_2690_ = lean_unbox(v_fst_2677_);
if (v___x_2690_ == 0)
{
uint8_t v___x_2691_; 
v___x_2691_ = lean_unbox(v_fst_2679_);
if (v___x_2691_ == 0)
{
v___y_2682_ = v___x_2656_;
goto v___jp_2681_;
}
else
{
lean_del_object(v___x_2672_);
goto v___jp_2674_;
}
}
else
{
uint8_t v___x_2692_; 
v___x_2692_ = lean_unbox(v_fst_2679_);
v___y_2682_ = v___x_2692_;
goto v___jp_2681_;
}
v___jp_2674_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2669_, v_val_2670_, v_x_2647_, v_x_2648_);
v___x_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
v___y_2664_ = v___x_2676_;
goto v___jp_2663_;
}
v___jp_2681_:
{
if (v___y_2682_ == 0)
{
lean_del_object(v___x_2672_);
goto v___jp_2674_;
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2683_ = lean_array_get_size(v_snd_2678_);
v___x_2684_ = lean_array_get_size(v_snd_2680_);
v___x_2685_ = lean_nat_dec_eq(v___x_2683_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_del_object(v___x_2672_);
goto v___jp_2674_;
}
else
{
uint8_t v___x_2686_; 
v___x_2686_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2678_, v_snd_2680_, v___x_2683_);
if (v___x_2686_ == 0)
{
lean_del_object(v___x_2672_);
goto v___jp_2674_;
}
else
{
lean_object* v___x_2688_; 
lean_dec(v_val_2670_);
lean_dec(v_key_2669_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v_x_2648_);
lean_ctor_set(v___x_2672_, 0, v_x_2647_);
v___x_2688_ = v___x_2672_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_x_2647_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_x_2648_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
v___y_2664_ = v___x_2688_;
goto v___jp_2663_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_node_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2704_; 
v_node_2694_ = lean_ctor_get(v_v_2660_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_v_2660_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2696_ = v_v_2660_;
v_isShared_2697_ = v_isSharedCheck_2704_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_node_2694_);
lean_dec(v_v_2660_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2704_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
size_t v___x_2698_; size_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2698_ = lean_usize_shift_right(v_x_2645_, v___x_2650_);
v___x_2699_ = lean_usize_add(v_x_2646_, v___x_2651_);
v___x_2700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_node_2694_, v___x_2698_, v___x_2699_, v_x_2647_, v_x_2648_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2700_);
v___x_2702_ = v___x_2696_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
v___y_2664_ = v___x_2702_;
goto v___jp_2663_;
}
}
}
default: 
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v_x_2647_);
lean_ctor_set(v___x_2705_, 1, v_x_2648_);
v___y_2664_ = v___x_2705_;
goto v___jp_2663_;
}
}
v___jp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2665_ = lean_array_fset(v_xs_x27_2662_, v_j_2654_, v___y_2664_);
lean_dec(v_j_2654_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2665_);
v___x_2667_ = v___x_2658_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
else
{
lean_object* v_ks_2708_; lean_object* v_vs_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2729_; 
v_ks_2708_ = lean_ctor_get(v_x_2644_, 0);
v_vs_2709_ = lean_ctor_get(v_x_2644_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2711_ = v_x_2644_;
v_isShared_2712_ = v_isSharedCheck_2729_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_vs_2709_);
lean_inc(v_ks_2708_);
lean_dec(v_x_2644_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2729_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_ks_2708_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_vs_2709_);
v___x_2714_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v_newNode_2715_; uint8_t v___y_2717_; size_t v___x_2723_; uint8_t v___x_2724_; 
v_newNode_2715_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(v___x_2714_, v_x_2647_, v_x_2648_);
v___x_2723_ = ((size_t)7ULL);
v___x_2724_ = lean_usize_dec_le(v___x_2723_, v_x_2646_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2725_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2715_);
v___x_2726_ = lean_unsigned_to_nat(4u);
v___x_2727_ = lean_nat_dec_lt(v___x_2725_, v___x_2726_);
lean_dec(v___x_2725_);
v___y_2717_ = v___x_2727_;
goto v___jp_2716_;
}
else
{
v___y_2717_ = v___x_2724_;
goto v___jp_2716_;
}
v___jp_2716_:
{
if (v___y_2717_ == 0)
{
lean_object* v_ks_2718_; lean_object* v_vs_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v_ks_2718_ = lean_ctor_get(v_newNode_2715_, 0);
lean_inc_ref(v_ks_2718_);
v_vs_2719_ = lean_ctor_get(v_newNode_2715_, 1);
lean_inc_ref(v_vs_2719_);
lean_dec_ref(v_newNode_2715_);
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2722_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2646_, v_ks_2718_, v_vs_2719_, v___x_2720_, v___x_2721_);
lean_dec_ref(v_vs_2719_);
lean_dec_ref(v_ks_2718_);
return v___x_2722_;
}
else
{
return v_newNode_2715_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_2730_, lean_object* v_keys_2731_, lean_object* v_vals_2732_, lean_object* v_i_2733_, lean_object* v_entries_2734_){
_start:
{
lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = lean_array_get_size(v_keys_2731_);
v___x_2736_ = lean_nat_dec_lt(v_i_2733_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_dec(v_i_2733_);
return v_entries_2734_;
}
else
{
lean_object* v_k_2737_; lean_object* v_fst_2738_; lean_object* v_snd_2739_; lean_object* v_v_2740_; uint64_t v___y_2742_; uint64_t v___y_2743_; uint64_t v___y_2756_; uint8_t v___x_2768_; 
v_k_2737_ = lean_array_fget_borrowed(v_keys_2731_, v_i_2733_);
v_fst_2738_ = lean_ctor_get(v_k_2737_, 0);
v_snd_2739_ = lean_ctor_get(v_k_2737_, 1);
v_v_2740_ = lean_array_fget_borrowed(v_vals_2732_, v_i_2733_);
v___x_2768_ = lean_unbox(v_fst_2738_);
if (v___x_2768_ == 0)
{
uint64_t v___x_2769_; 
v___x_2769_ = 13ULL;
v___y_2756_ = v___x_2769_;
goto v___jp_2755_;
}
else
{
uint64_t v___x_2770_; 
v___x_2770_ = 11ULL;
v___y_2756_ = v___x_2770_;
goto v___jp_2755_;
}
v___jp_2741_:
{
uint64_t v___x_2744_; size_t v_h_2745_; size_t v___x_2746_; lean_object* v___x_2747_; size_t v___x_2748_; size_t v___x_2749_; size_t v___x_2750_; size_t v_h_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2744_ = lean_uint64_mix_hash(v___y_2742_, v___y_2743_);
v_h_2745_ = lean_uint64_to_usize(v___x_2744_);
v___x_2746_ = ((size_t)5ULL);
v___x_2747_ = lean_unsigned_to_nat(1u);
v___x_2748_ = ((size_t)1ULL);
v___x_2749_ = lean_usize_sub(v_depth_2730_, v___x_2748_);
v___x_2750_ = lean_usize_mul(v___x_2746_, v___x_2749_);
v_h_2751_ = lean_usize_shift_right(v_h_2745_, v___x_2750_);
v___x_2752_ = lean_nat_add(v_i_2733_, v___x_2747_);
lean_dec(v_i_2733_);
lean_inc(v_v_2740_);
lean_inc(v_k_2737_);
v___x_2753_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_entries_2734_, v_h_2751_, v_depth_2730_, v_k_2737_, v_v_2740_);
v_i_2733_ = v___x_2752_;
v_entries_2734_ = v___x_2753_;
goto _start;
}
v___jp_2755_:
{
uint64_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2757_ = 7ULL;
v___x_2758_ = lean_unsigned_to_nat(0u);
v___x_2759_ = lean_array_get_size(v_snd_2739_);
v___x_2760_ = lean_nat_dec_lt(v___x_2758_, v___x_2759_);
if (v___x_2760_ == 0)
{
v___y_2742_ = v___y_2756_;
v___y_2743_ = v___x_2757_;
goto v___jp_2741_;
}
else
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_nat_dec_le(v___x_2759_, v___x_2759_);
if (v___x_2761_ == 0)
{
if (v___x_2760_ == 0)
{
v___y_2742_ = v___y_2756_;
v___y_2743_ = v___x_2757_;
goto v___jp_2741_;
}
else
{
size_t v___x_2762_; size_t v___x_2763_; uint64_t v___x_2764_; 
v___x_2762_ = ((size_t)0ULL);
v___x_2763_ = lean_usize_of_nat(v___x_2759_);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2739_, v___x_2762_, v___x_2763_, v___x_2757_);
v___y_2742_ = v___y_2756_;
v___y_2743_ = v___x_2764_;
goto v___jp_2741_;
}
}
else
{
size_t v___x_2765_; size_t v___x_2766_; uint64_t v___x_2767_; 
v___x_2765_ = ((size_t)0ULL);
v___x_2766_ = lean_usize_of_nat(v___x_2759_);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2739_, v___x_2765_, v___x_2766_, v___x_2757_);
v___y_2742_ = v___y_2756_;
v___y_2743_ = v___x_2767_;
goto v___jp_2741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_2771_, lean_object* v_keys_2772_, lean_object* v_vals_2773_, lean_object* v_i_2774_, lean_object* v_entries_2775_){
_start:
{
size_t v_depth_boxed_2776_; lean_object* v_res_2777_; 
v_depth_boxed_2776_ = lean_unbox_usize(v_depth_2771_);
lean_dec(v_depth_2771_);
v_res_2777_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_2776_, v_keys_2772_, v_vals_2773_, v_i_2774_, v_entries_2775_);
lean_dec_ref(v_vals_2773_);
lean_dec_ref(v_keys_2772_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2778_, lean_object* v_x_2779_, lean_object* v_x_2780_, lean_object* v_x_2781_, lean_object* v_x_2782_){
_start:
{
size_t v_x_2154__boxed_2783_; size_t v_x_2155__boxed_2784_; lean_object* v_res_2785_; 
v_x_2154__boxed_2783_ = lean_unbox_usize(v_x_2779_);
lean_dec(v_x_2779_);
v_x_2155__boxed_2784_ = lean_unbox_usize(v_x_2780_);
lean_dec(v_x_2780_);
v_res_2785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2778_, v_x_2154__boxed_2783_, v_x_2155__boxed_2784_, v_x_2781_, v_x_2782_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(lean_object* v_x_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
uint64_t v___y_2790_; uint64_t v___y_2791_; lean_object* v_fst_2796_; lean_object* v_snd_2797_; uint64_t v___y_2799_; uint8_t v___x_2811_; 
v_fst_2796_ = lean_ctor_get(v_x_2787_, 0);
v_snd_2797_ = lean_ctor_get(v_x_2787_, 1);
v___x_2811_ = lean_unbox(v_fst_2796_);
if (v___x_2811_ == 0)
{
uint64_t v___x_2812_; 
v___x_2812_ = 13ULL;
v___y_2799_ = v___x_2812_;
goto v___jp_2798_;
}
else
{
uint64_t v___x_2813_; 
v___x_2813_ = 11ULL;
v___y_2799_ = v___x_2813_;
goto v___jp_2798_;
}
v___jp_2789_:
{
uint64_t v___x_2792_; size_t v___x_2793_; size_t v___x_2794_; lean_object* v___x_2795_; 
v___x_2792_ = lean_uint64_mix_hash(v___y_2790_, v___y_2791_);
v___x_2793_ = lean_uint64_to_usize(v___x_2792_);
v___x_2794_ = ((size_t)1ULL);
v___x_2795_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2786_, v___x_2793_, v___x_2794_, v_x_2787_, v_x_2788_);
return v___x_2795_;
}
v___jp_2798_:
{
uint64_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2800_ = 7ULL;
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = lean_array_get_size(v_snd_2797_);
v___x_2803_ = lean_nat_dec_lt(v___x_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
v___y_2790_ = v___y_2799_;
v___y_2791_ = v___x_2800_;
goto v___jp_2789_;
}
else
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_nat_dec_le(v___x_2802_, v___x_2802_);
if (v___x_2804_ == 0)
{
if (v___x_2803_ == 0)
{
v___y_2790_ = v___y_2799_;
v___y_2791_ = v___x_2800_;
goto v___jp_2789_;
}
else
{
size_t v___x_2805_; size_t v___x_2806_; uint64_t v___x_2807_; 
v___x_2805_ = ((size_t)0ULL);
v___x_2806_ = lean_usize_of_nat(v___x_2802_);
v___x_2807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2797_, v___x_2805_, v___x_2806_, v___x_2800_);
v___y_2790_ = v___y_2799_;
v___y_2791_ = v___x_2807_;
goto v___jp_2789_;
}
}
else
{
size_t v___x_2808_; size_t v___x_2809_; uint64_t v___x_2810_; 
v___x_2808_ = ((size_t)0ULL);
v___x_2809_ = lean_usize_of_nat(v___x_2802_);
v___x_2810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2797_, v___x_2808_, v___x_2809_, v___x_2800_);
v___y_2790_ = v___y_2799_;
v___y_2791_ = v___x_2810_;
goto v___jp_2789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(lean_object* v_x_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_){
_start:
{
uint8_t v_stage_u2081_2817_; 
v_stage_u2081_2817_ = lean_ctor_get_uint8(v_x_2814_, sizeof(void*)*2);
if (v_stage_u2081_2817_ == 0)
{
lean_object* v_map_u2081_2818_; lean_object* v_map_u2082_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2827_; 
v_map_u2081_2818_ = lean_ctor_get(v_x_2814_, 0);
v_map_u2082_2819_ = lean_ctor_get(v_x_2814_, 1);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_x_2814_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2821_ = v_x_2814_;
v_isShared_2822_ = v_isSharedCheck_2827_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_map_u2082_2819_);
lean_inc(v_map_u2081_2818_);
lean_dec(v_x_2814_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2827_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2823_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_map_u2082_2819_, v_x_2815_, v_x_2816_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 1, v___x_2823_);
v___x_2825_ = v___x_2821_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_map_u2081_2818_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v___x_2823_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, sizeof(void*)*2, v_stage_u2081_2817_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
else
{
lean_object* v_map_u2081_2828_; lean_object* v_map_u2082_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2837_; 
v_map_u2081_2828_ = lean_ctor_get(v_x_2814_, 0);
v_map_u2082_2829_ = lean_ctor_get(v_x_2814_, 1);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_x_2814_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2831_ = v_x_2814_;
v_isShared_2832_ = v_isSharedCheck_2837_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_map_u2082_2829_);
lean_inc(v_map_u2081_2828_);
lean_dec(v_x_2814_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2837_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2833_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_map_u2081_2828_, v_x_2815_, v_x_2816_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2833_);
v___x_2835_ = v___x_2831_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_map_u2082_2829_);
lean_ctor_set_uint8(v_reuseFailAlloc_2836_, sizeof(void*)*2, v_stage_u2081_2817_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminatorEntry(lean_object* v_es_2838_, lean_object* v_e_2839_){
_start:
{
uint8_t v_induction_2840_; lean_object* v_typeNames_2841_; lean_object* v_elimName_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v_induction_2840_ = lean_ctor_get_uint8(v_e_2839_, sizeof(void*)*2);
v_typeNames_2841_ = lean_ctor_get(v_e_2839_, 0);
lean_inc_ref(v_typeNames_2841_);
v_elimName_2842_ = lean_ctor_get(v_e_2839_, 1);
lean_inc(v_elimName_2842_);
lean_dec_ref(v_e_2839_);
v___x_2843_ = lean_box(v_induction_2840_);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v_typeNames_2841_);
v___x_2845_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(v_es_2838_, v___x_2844_, v_elimName_2842_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0(lean_object* v_00_u03b2_2846_, lean_object* v_x_2847_, lean_object* v_x_2848_, lean_object* v_x_2849_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(v_x_2847_, v_x_2848_, v_x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(lean_object* v_00_u03b2_2851_, lean_object* v_x_2852_, lean_object* v_x_2853_, lean_object* v_x_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_x_2852_, v_x_2853_, v_x_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1(lean_object* v_00_u03b2_2856_, lean_object* v_m_2857_, lean_object* v_a_2858_, lean_object* v_b_2859_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_m_2857_, v_a_2858_, v_b_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2861_, lean_object* v_x_2862_, size_t v_x_2863_, size_t v_x_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2862_, v_x_2863_, v_x_2864_, v_x_2865_, v_x_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2868_, lean_object* v_x_2869_, lean_object* v_x_2870_, lean_object* v_x_2871_, lean_object* v_x_2872_, lean_object* v_x_2873_){
_start:
{
size_t v_x_2486__boxed_2874_; size_t v_x_2487__boxed_2875_; lean_object* v_res_2876_; 
v_x_2486__boxed_2874_ = lean_unbox_usize(v_x_2870_);
lean_dec(v_x_2870_);
v_x_2487__boxed_2875_ = lean_unbox_usize(v_x_2871_);
lean_dec(v_x_2871_);
v_res_2876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(v_00_u03b2_2868_, v_x_2869_, v_x_2486__boxed_2874_, v_x_2487__boxed_2875_, v_x_2872_, v_x_2873_);
return v_res_2876_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2877_, lean_object* v_a_2878_, lean_object* v_x_2879_){
_start:
{
uint8_t v___x_2880_; 
v___x_2880_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2878_, v_x_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2881_, lean_object* v_a_2882_, lean_object* v_x_2883_){
_start:
{
uint8_t v_res_2884_; lean_object* v_r_2885_; 
v_res_2884_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(v_00_u03b2_2881_, v_a_2882_, v_x_2883_);
lean_dec(v_x_2883_);
lean_dec_ref(v_a_2882_);
v_r_2885_ = lean_box(v_res_2884_);
return v_r_2885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2886_, lean_object* v_data_2887_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(v_data_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_2889_, lean_object* v_a_2890_, lean_object* v_b_2891_, lean_object* v_x_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2890_, v_b_2891_, v_x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_xs_2894_, lean_object* v_ys_2895_, lean_object* v_hsz_2896_, lean_object* v_x_2897_, lean_object* v_x_2898_){
_start:
{
uint8_t v___x_2899_; 
v___x_2899_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_2894_, v_ys_2895_, v_x_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_xs_2900_, lean_object* v_ys_2901_, lean_object* v_hsz_2902_, lean_object* v_x_2903_, lean_object* v_x_2904_){
_start:
{
uint8_t v_res_2905_; lean_object* v_r_2906_; 
v_res_2905_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(v_xs_2900_, v_ys_2901_, v_hsz_2902_, v_x_2903_, v_x_2904_);
lean_dec_ref(v_ys_2901_);
lean_dec_ref(v_xs_2900_);
v_r_2906_ = lean_box(v_res_2905_);
return v_r_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2907_, lean_object* v_n_2908_, lean_object* v_k_2909_, lean_object* v_v_2910_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_n_2908_, v_k_2909_, v_v_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2912_, size_t v_depth_2913_, lean_object* v_keys_2914_, lean_object* v_vals_2915_, lean_object* v_heq_2916_, lean_object* v_i_2917_, lean_object* v_entries_2918_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_2913_, v_keys_2914_, v_vals_2915_, v_i_2917_, v_entries_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2920_, lean_object* v_depth_2921_, lean_object* v_keys_2922_, lean_object* v_vals_2923_, lean_object* v_heq_2924_, lean_object* v_i_2925_, lean_object* v_entries_2926_){
_start:
{
size_t v_depth_boxed_2927_; lean_object* v_res_2928_; 
v_depth_boxed_2927_ = lean_unbox_usize(v_depth_2921_);
lean_dec(v_depth_2921_);
v_res_2928_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_2920_, v_depth_boxed_2927_, v_keys_2922_, v_vals_2923_, v_heq_2924_, v_i_2925_, v_entries_2926_);
lean_dec_ref(v_vals_2923_);
lean_dec_ref(v_keys_2922_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03b2_2929_, lean_object* v_i_2930_, lean_object* v_source_2931_, lean_object* v_target_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(v_i_2930_, v_source_2931_, v_target_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2934_, lean_object* v_x_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_, lean_object* v_x_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_x_2935_, v_x_2936_, v_x_2937_, v_x_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_2940_, lean_object* v_x_2941_, lean_object* v_x_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(v_x_2941_, v_x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_2944_){
_start:
{
uint8_t v_stage_u2081_2945_; 
v_stage_u2081_2945_ = lean_ctor_get_uint8(v_m_2944_, sizeof(void*)*2);
if (v_stage_u2081_2945_ == 0)
{
return v_m_2944_;
}
else
{
lean_object* v_map_u2081_2946_; lean_object* v_map_u2082_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2955_; 
v_map_u2081_2946_ = lean_ctor_get(v_m_2944_, 0);
v_map_u2082_2947_ = lean_ctor_get(v_m_2944_, 1);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_m_2944_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2949_ = v_m_2944_;
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_map_u2082_2947_);
lean_inc(v_map_u2081_2946_);
lean_dec(v_m_2944_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
uint8_t v___x_2951_; lean_object* v___x_2953_; 
v___x_2951_ = 0;
if (v_isShared_2950_ == 0)
{
v___x_2953_ = v___x_2949_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_map_u2081_2946_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_map_u2082_2947_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*2, v___x_2951_);
return v___x_2953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_2956_, lean_object* v_m_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_SMap_switch___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(v_m_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(uint8_t v_x_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___y_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object* v_x_2962_, lean_object* v___y_2963_){
_start:
{
uint8_t v_x_124__boxed_2964_; lean_object* v_res_2965_; 
v_x_124__boxed_2964_ = lean_unbox(v_x_2962_);
v_res_2965_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(v_x_124__boxed_2964_, v___y_2963_);
return v_res_2965_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2976_; lean_object* v___f_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___f_2976_ = ((lean_object*)(l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___f_2977_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2978_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4);
v___x_2979_ = ((lean_object*)(l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2980_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
lean_ctor_set(v___x_2981_, 1, v___x_2979_);
lean_ctor_set(v___x_2981_, 2, v___x_2978_);
lean_ctor_set(v___x_2981_, 3, v___f_2977_);
lean_ctor_set(v___x_2981_, 4, v___f_2976_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = lean_obj_once(&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_);
v___x_2984_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object* v_a_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
return v_res_2986_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(lean_object* v_x_2987_){
_start:
{
uint8_t v___x_2988_; 
v___x_2988_ = 0;
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed(lean_object* v_x_2989_){
_start:
{
uint8_t v_res_2990_; lean_object* v_r_2991_; 
v_res_2990_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(v_x_2989_);
lean_dec(v_x_2989_);
v_r_2991_ = lean_box(v_res_2990_);
return v_r_2991_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(lean_object* v_fvarId_2992_, lean_object* v_x_2993_){
_start:
{
uint8_t v___x_2994_; 
v___x_2994_ = l_Lean_instBEqFVarId_beq(v_fvarId_2992_, v_x_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_2995_, lean_object* v_x_2996_){
_start:
{
uint8_t v_res_2997_; lean_object* v_r_2998_; 
v_res_2997_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(v_fvarId_2995_, v_x_2996_);
lean_dec(v_x_2996_);
lean_dec(v_fvarId_2995_);
v_r_2998_ = lean_box(v_res_2997_);
return v_r_2998_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = lean_box(0);
v___x_3001_ = lean_unsigned_to_nat(16u);
v___x_3002_ = lean_mk_array(v___x_3001_, v___x_3000_);
return v___x_3002_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3003_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1);
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
lean_ctor_set(v___x_3005_, 1, v___x_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(lean_object* v_e_3006_, lean_object* v_fvarId_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; uint8_t v_fst_3012_; lean_object* v_mctx_3013_; lean_object* v___y_3031_; lean_object* v_mctx_3036_; lean_object* v___f_3037_; lean_object* v___f_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3010_ = lean_st_ref_get(v___y_3008_);
v_mctx_3036_ = lean_ctor_get(v___x_3010_, 0);
lean_inc_ref(v_mctx_3036_);
lean_dec(v___x_3010_);
v___f_3037_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0));
v___f_3038_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3038_, 0, v_fvarId_3007_);
v___x_3039_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2);
lean_inc_ref(v_mctx_3036_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v_mctx_3036_);
v___x_3041_ = l_Lean_Expr_hasFVar(v_e_3006_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; 
v___x_3042_ = l_Lean_Expr_hasMVar(v_e_3006_);
if (v___x_3042_ == 0)
{
lean_dec_ref(v___x_3040_);
lean_dec_ref(v___f_3038_);
lean_dec_ref(v_e_3006_);
v_fst_3012_ = v___x_3042_;
v_mctx_3013_ = v_mctx_3036_;
goto v___jp_3011_;
}
else
{
lean_object* v___x_3043_; 
lean_dec_ref(v_mctx_3036_);
v___x_3043_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3038_, v___f_3037_, v_e_3006_, v___x_3040_);
v___y_3031_ = v___x_3043_;
goto v___jp_3030_;
}
}
else
{
lean_object* v___x_3044_; 
lean_dec_ref(v_mctx_3036_);
v___x_3044_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3038_, v___f_3037_, v_e_3006_, v___x_3040_);
v___y_3031_ = v___x_3044_;
goto v___jp_3030_;
}
v___jp_3011_:
{
lean_object* v___x_3014_; lean_object* v_cache_3015_; lean_object* v_zetaDeltaFVarIds_3016_; lean_object* v_postponed_3017_; lean_object* v_diag_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3028_; 
v___x_3014_ = lean_st_ref_take(v___y_3008_);
v_cache_3015_ = lean_ctor_get(v___x_3014_, 1);
v_zetaDeltaFVarIds_3016_ = lean_ctor_get(v___x_3014_, 2);
v_postponed_3017_ = lean_ctor_get(v___x_3014_, 3);
v_diag_3018_ = lean_ctor_get(v___x_3014_, 4);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3028_ == 0)
{
lean_object* v_unused_3029_; 
v_unused_3029_ = lean_ctor_get(v___x_3014_, 0);
lean_dec(v_unused_3029_);
v___x_3020_ = v___x_3014_;
v_isShared_3021_ = v_isSharedCheck_3028_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_diag_3018_);
lean_inc(v_postponed_3017_);
lean_inc(v_zetaDeltaFVarIds_3016_);
lean_inc(v_cache_3015_);
lean_dec(v___x_3014_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3028_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v_mctx_3013_);
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_mctx_3013_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_cache_3015_);
lean_ctor_set(v_reuseFailAlloc_3027_, 2, v_zetaDeltaFVarIds_3016_);
lean_ctor_set(v_reuseFailAlloc_3027_, 3, v_postponed_3017_);
lean_ctor_set(v_reuseFailAlloc_3027_, 4, v_diag_3018_);
v___x_3023_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = lean_st_ref_set(v___y_3008_, v___x_3023_);
v___x_3025_ = lean_box(v_fst_3012_);
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
return v___x_3026_;
}
}
}
v___jp_3030_:
{
lean_object* v_snd_3032_; lean_object* v_fst_3033_; lean_object* v_mctx_3034_; uint8_t v___x_3035_; 
v_snd_3032_ = lean_ctor_get(v___y_3031_, 1);
lean_inc(v_snd_3032_);
v_fst_3033_ = lean_ctor_get(v___y_3031_, 0);
lean_inc(v_fst_3033_);
lean_dec_ref(v___y_3031_);
v_mctx_3034_ = lean_ctor_get(v_snd_3032_, 1);
lean_inc_ref(v_mctx_3034_);
lean_dec(v_snd_3032_);
v___x_3035_ = lean_unbox(v_fst_3033_);
lean_dec(v_fst_3033_);
v_fst_3012_ = v___x_3035_;
v_mctx_3013_ = v_mctx_3034_;
goto v___jp_3011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___boxed(lean_object* v_e_3045_, lean_object* v_fvarId_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_e_3045_, v_fvarId_3046_, v___y_3047_);
lean_dec(v___y_3047_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(lean_object* v_e_3050_, lean_object* v_fvarId_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_e_3050_, v_fvarId_3051_, v___y_3053_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___boxed(lean_object* v_e_3058_, lean_object* v_fvarId_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(v_e_3058_, v_fvarId_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(lean_object* v_upperBound_3069_, lean_object* v___x_3070_, lean_object* v_xs_3071_, lean_object* v___x_3072_, lean_object* v_a_3073_, lean_object* v_b_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
uint8_t v___x_3080_; 
v___x_3080_ = lean_nat_dec_lt(v_a_3073_, v_upperBound_3069_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; 
lean_dec(v_a_3073_);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v_b_3074_);
return v___x_3081_;
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_dec_ref(v_b_3074_);
v___x_3082_ = l_Lean_instInhabitedExpr;
v___x_3083_ = lean_array_fget_borrowed(v___x_3070_, v_a_3073_);
v___x_3084_ = lean_array_get_borrowed(v___x_3082_, v_xs_3071_, v___x_3083_);
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
lean_inc(v___x_3084_);
v___x_3085_ = lean_infer_type(v___x_3084_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref(v___x_3085_);
v___x_3087_ = l_Lean_Expr_fvarId_x21(v___x_3072_);
v___x_3088_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_a_3086_, v___x_3087_, v___y_3076_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3104_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3104_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3104_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; uint8_t v___x_3094_; 
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_unbox(v_a_3089_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
lean_del_object(v___x_3091_);
lean_dec(v_a_3089_);
v___x_3095_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0));
v___x_3096_ = lean_unsigned_to_nat(1u);
v___x_3097_ = lean_nat_add(v_a_3073_, v___x_3096_);
lean_dec(v_a_3073_);
v_a_3073_ = v___x_3097_;
v_b_3074_ = v___x_3095_;
goto _start;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
lean_dec(v_a_3073_);
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v_a_3089_);
v___x_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
lean_ctor_set(v___x_3100_, 1, v___x_3093_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3100_);
v___x_3102_ = v___x_3091_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3100_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_a_3073_);
v_a_3105_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3088_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3088_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v_a_3073_);
v_a_3113_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3085_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3085_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___boxed(lean_object* v_upperBound_3121_, lean_object* v___x_3122_, lean_object* v_xs_3123_, lean_object* v___x_3124_, lean_object* v_a_3125_, lean_object* v_b_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v_upperBound_3121_, v___x_3122_, v_xs_3123_, v___x_3124_, v_a_3125_, v_b_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec_ref(v___x_3124_);
lean_dec_ref(v_xs_3123_);
lean_dec_ref(v___x_3122_);
lean_dec(v_upperBound_3121_);
return v_res_3132_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0));
v___x_3135_ = l_Lean_stringToMessageData(v___x_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(lean_object* v_upperBound_3136_, lean_object* v___x_3137_, lean_object* v___x_3138_, lean_object* v_xs_3139_, lean_object* v_a_3140_, lean_object* v_b_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_a_3148_; uint8_t v___x_3152_; 
v___x_3152_ = lean_nat_dec_lt(v_a_3140_, v_upperBound_3136_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
lean_dec(v_a_3140_);
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v_b_3141_);
return v___x_3153_;
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3154_ = l_Lean_instInhabitedExpr;
v___x_3155_ = lean_unsigned_to_nat(1u);
v___x_3156_ = lean_nat_add(v_a_3140_, v___x_3155_);
v___x_3157_ = lean_array_fget_borrowed(v___x_3138_, v_a_3140_);
v___x_3158_ = lean_array_get_borrowed(v___x_3154_, v_xs_3139_, v___x_3157_);
v___x_3185_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0));
v___x_3186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v___x_3137_, v___x_3138_, v_xs_3139_, v___x_3158_, v___x_3156_, v___x_3185_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; lean_object* v_fst_3188_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref(v___x_3186_);
v_fst_3188_ = lean_ctor_get(v_a_3187_, 0);
lean_inc(v_fst_3188_);
lean_dec(v_a_3187_);
if (lean_obj_tag(v_fst_3188_) == 0)
{
goto v___jp_3159_;
}
else
{
lean_object* v_val_3189_; uint8_t v___x_3190_; 
v_val_3189_ = lean_ctor_get(v_fst_3188_, 0);
lean_inc(v_val_3189_);
lean_dec_ref(v_fst_3188_);
v___x_3190_ = lean_unbox(v_val_3189_);
lean_dec(v_val_3189_);
if (v___x_3190_ == 0)
{
goto v___jp_3159_;
}
else
{
v_a_3148_ = v_b_3141_;
goto v___jp_3147_;
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec_ref(v_b_3141_);
lean_dec(v_a_3140_);
v_a_3191_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3186_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3186_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
v___jp_3159_:
{
lean_object* v___x_3160_; 
lean_inc(v___y_3145_);
lean_inc_ref(v___y_3144_);
lean_inc(v___y_3143_);
lean_inc_ref(v___y_3142_);
lean_inc(v___x_3158_);
v___x_3160_ = lean_infer_type(v___x_3158_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3162_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref(v___x_3160_);
v___x_3162_ = l_Lean_Expr_getAppFn(v_a_3161_);
if (lean_obj_tag(v___x_3162_) == 4)
{
lean_object* v_declName_3163_; lean_object* v___x_3164_; 
lean_dec(v_a_3161_);
v_declName_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_declName_3163_);
lean_dec_ref(v___x_3162_);
v___x_3164_ = lean_array_push(v_b_3141_, v_declName_3163_);
v_a_3148_ = v___x_3164_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_dec_ref(v___x_3162_);
v___x_3165_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1);
v___x_3166_ = l_Lean_indentExpr(v_a_3161_);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_3167_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_dec_ref(v___x_3168_);
v_a_3148_ = v_b_3141_;
goto v___jp_3147_;
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref(v_b_3141_);
lean_dec(v_a_3140_);
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3168_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3168_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec_ref(v_b_3141_);
lean_dec(v_a_3140_);
v_a_3177_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3160_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3160_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
v___jp_3147_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = lean_unsigned_to_nat(1u);
v___x_3150_ = lean_nat_add(v_a_3140_, v___x_3149_);
lean_dec(v_a_3140_);
v_a_3140_ = v___x_3150_;
v_b_3141_ = v_a_3148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___boxed(lean_object* v_upperBound_3199_, lean_object* v___x_3200_, lean_object* v___x_3201_, lean_object* v_xs_3202_, lean_object* v_a_3203_, lean_object* v_b_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v_upperBound_3199_, v___x_3200_, v___x_3201_, v_xs_3202_, v_a_3203_, v_b_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec_ref(v_xs_3202_);
lean_dec_ref(v___x_3201_);
lean_dec(v___x_3200_);
lean_dec(v_upperBound_3199_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0(lean_object* v_a_3211_, uint8_t v_induction_3212_, lean_object* v_elimName_3213_, lean_object* v_xs_3214_, lean_object* v_x_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_targetsPos_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v_targetsPos_3221_ = lean_ctor_get(v_a_3211_, 3);
v___x_3222_ = lean_array_get_size(v_targetsPos_3221_);
v___x_3223_ = lean_unsigned_to_nat(0u);
v___x_3224_ = ((lean_object*)(l_Lean_Meta_addImplicitTargets___closed__0));
v___x_3225_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v___x_3222_, v___x_3222_, v_targetsPos_3221_, v_xs_3214_, v___x_3223_, v___x_3224_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3234_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3234_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3234_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3230_, 0, v_a_3226_);
lean_ctor_set(v___x_3230_, 1, v_elimName_3213_);
lean_ctor_set_uint8(v___x_3230_, sizeof(void*)*2, v_induction_3212_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3230_);
v___x_3232_ = v___x_3228_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec(v_elimName_3213_);
v_a_3235_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3225_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3225_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0___boxed(lean_object* v_a_3243_, lean_object* v_induction_3244_, lean_object* v_elimName_3245_, lean_object* v_xs_3246_, lean_object* v_x_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
uint8_t v_induction_boxed_3253_; lean_object* v_res_3254_; 
v_induction_boxed_3253_ = lean_unbox(v_induction_3244_);
v_res_3254_ = l_Lean_Meta_mkCustomEliminator___lam__0(v_a_3243_, v_induction_boxed_3253_, v_elimName_3245_, v_xs_3246_, v_x_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec_ref(v_x_3247_);
lean_dec_ref(v_xs_3246_);
lean_dec_ref(v_a_3243_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(lean_object* v_ref_3255_, lean_object* v_msg_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_fileName_3262_; lean_object* v_fileMap_3263_; lean_object* v_options_3264_; lean_object* v_currRecDepth_3265_; lean_object* v_maxRecDepth_3266_; lean_object* v_ref_3267_; lean_object* v_currNamespace_3268_; lean_object* v_openDecls_3269_; lean_object* v_initHeartbeats_3270_; lean_object* v_maxHeartbeats_3271_; lean_object* v_quotContext_3272_; lean_object* v_currMacroScope_3273_; uint8_t v_diag_3274_; lean_object* v_cancelTk_x3f_3275_; uint8_t v_suppressElabErrors_3276_; lean_object* v_inheritedTraceOptions_3277_; lean_object* v_ref_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_fileName_3262_ = lean_ctor_get(v___y_3259_, 0);
v_fileMap_3263_ = lean_ctor_get(v___y_3259_, 1);
v_options_3264_ = lean_ctor_get(v___y_3259_, 2);
v_currRecDepth_3265_ = lean_ctor_get(v___y_3259_, 3);
v_maxRecDepth_3266_ = lean_ctor_get(v___y_3259_, 4);
v_ref_3267_ = lean_ctor_get(v___y_3259_, 5);
v_currNamespace_3268_ = lean_ctor_get(v___y_3259_, 6);
v_openDecls_3269_ = lean_ctor_get(v___y_3259_, 7);
v_initHeartbeats_3270_ = lean_ctor_get(v___y_3259_, 8);
v_maxHeartbeats_3271_ = lean_ctor_get(v___y_3259_, 9);
v_quotContext_3272_ = lean_ctor_get(v___y_3259_, 10);
v_currMacroScope_3273_ = lean_ctor_get(v___y_3259_, 11);
v_diag_3274_ = lean_ctor_get_uint8(v___y_3259_, sizeof(void*)*14);
v_cancelTk_x3f_3275_ = lean_ctor_get(v___y_3259_, 12);
v_suppressElabErrors_3276_ = lean_ctor_get_uint8(v___y_3259_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3277_ = lean_ctor_get(v___y_3259_, 13);
v_ref_3278_ = l_Lean_replaceRef(v_ref_3255_, v_ref_3267_);
lean_inc_ref(v_inheritedTraceOptions_3277_);
lean_inc(v_cancelTk_x3f_3275_);
lean_inc(v_currMacroScope_3273_);
lean_inc(v_quotContext_3272_);
lean_inc(v_maxHeartbeats_3271_);
lean_inc(v_initHeartbeats_3270_);
lean_inc(v_openDecls_3269_);
lean_inc(v_currNamespace_3268_);
lean_inc(v_maxRecDepth_3266_);
lean_inc(v_currRecDepth_3265_);
lean_inc_ref(v_options_3264_);
lean_inc_ref(v_fileMap_3263_);
lean_inc_ref(v_fileName_3262_);
v___x_3279_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3279_, 0, v_fileName_3262_);
lean_ctor_set(v___x_3279_, 1, v_fileMap_3263_);
lean_ctor_set(v___x_3279_, 2, v_options_3264_);
lean_ctor_set(v___x_3279_, 3, v_currRecDepth_3265_);
lean_ctor_set(v___x_3279_, 4, v_maxRecDepth_3266_);
lean_ctor_set(v___x_3279_, 5, v_ref_3278_);
lean_ctor_set(v___x_3279_, 6, v_currNamespace_3268_);
lean_ctor_set(v___x_3279_, 7, v_openDecls_3269_);
lean_ctor_set(v___x_3279_, 8, v_initHeartbeats_3270_);
lean_ctor_set(v___x_3279_, 9, v_maxHeartbeats_3271_);
lean_ctor_set(v___x_3279_, 10, v_quotContext_3272_);
lean_ctor_set(v___x_3279_, 11, v_currMacroScope_3273_);
lean_ctor_set(v___x_3279_, 12, v_cancelTk_x3f_3275_);
lean_ctor_set(v___x_3279_, 13, v_inheritedTraceOptions_3277_);
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*14, v_diag_3274_);
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*14 + 1, v_suppressElabErrors_3276_);
v___x_3280_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_3256_, v___y_3257_, v___y_3258_, v___x_3279_, v___y_3260_);
lean_dec_ref(v___x_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3281_, lean_object* v_msg_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3281_, v_msg_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v_ref_3281_);
return v_res_3288_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3289_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
return v___x_3291_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3293_ = lean_unsigned_to_nat(0u);
v___x_3294_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
lean_ctor_set(v___x_3294_, 2, v___x_3293_);
lean_ctor_set(v___x_3294_, 3, v___x_3292_);
lean_ctor_set(v___x_3294_, 4, v___x_3292_);
lean_ctor_set(v___x_3294_, 5, v___x_3292_);
lean_ctor_set(v___x_3294_, 6, v___x_3292_);
lean_ctor_set(v___x_3294_, 7, v___x_3292_);
lean_ctor_set(v___x_3294_, 8, v___x_3292_);
return v___x_3294_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = lean_unsigned_to_nat(32u);
v___x_3296_ = lean_mk_empty_array_with_capacity(v___x_3295_);
v___x_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3298_ = ((size_t)5ULL);
v___x_3299_ = lean_unsigned_to_nat(0u);
v___x_3300_ = lean_unsigned_to_nat(32u);
v___x_3301_ = lean_mk_empty_array_with_capacity(v___x_3300_);
v___x_3302_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3303_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v___x_3301_);
lean_ctor_set(v___x_3303_, 2, v___x_3299_);
lean_ctor_set(v___x_3303_, 3, v___x_3299_);
lean_ctor_set_usize(v___x_3303_, 4, v___x_3298_);
return v___x_3303_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3304_ = lean_box(1);
v___x_3305_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_3306_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
lean_ctor_set(v___x_3307_, 1, v___x_3305_);
lean_ctor_set(v___x_3307_, 2, v___x_3304_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
return v___x_3313_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
return v___x_3316_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_3319_ = l_Lean_stringToMessageData(v___x_3318_);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_3325_ = l_Lean_stringToMessageData(v___x_3324_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_3328_ = l_Lean_stringToMessageData(v___x_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3329_, lean_object* v_declHint_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v___x_3333_; lean_object* v_env_3334_; uint8_t v___x_3335_; 
v___x_3333_ = lean_st_ref_get(v___y_3331_);
v_env_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc_ref(v_env_3334_);
lean_dec(v___x_3333_);
v___x_3335_ = l_Lean_Name_isAnonymous(v_declHint_3330_);
if (v___x_3335_ == 0)
{
uint8_t v_isExporting_3336_; 
v_isExporting_3336_ = lean_ctor_get_uint8(v_env_3334_, sizeof(void*)*8);
if (v_isExporting_3336_ == 0)
{
lean_object* v___x_3337_; 
lean_dec_ref(v_env_3334_);
lean_dec(v_declHint_3330_);
v___x_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_msg_3329_);
return v___x_3337_;
}
else
{
lean_object* v___x_3338_; uint8_t v___x_3339_; 
lean_inc_ref(v_env_3334_);
v___x_3338_ = l_Lean_Environment_setExporting(v_env_3334_, v___x_3335_);
lean_inc(v_declHint_3330_);
lean_inc_ref(v___x_3338_);
v___x_3339_ = l_Lean_Environment_contains(v___x_3338_, v_declHint_3330_, v_isExporting_3336_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; 
lean_dec_ref(v___x_3338_);
lean_dec_ref(v_env_3334_);
lean_dec(v_declHint_3330_);
v___x_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3340_, 0, v_msg_3329_);
return v___x_3340_;
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v_c_3346_; lean_object* v___x_3347_; 
v___x_3341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_3342_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_3343_ = l_Lean_Options_empty;
v___x_3344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3338_);
lean_ctor_set(v___x_3344_, 1, v___x_3341_);
lean_ctor_set(v___x_3344_, 2, v___x_3342_);
lean_ctor_set(v___x_3344_, 3, v___x_3343_);
lean_inc(v_declHint_3330_);
v___x_3345_ = l_Lean_MessageData_ofConstName(v_declHint_3330_, v___x_3335_);
v_c_3346_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3346_, 0, v___x_3344_);
lean_ctor_set(v_c_3346_, 1, v___x_3345_);
v___x_3347_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3334_, v_declHint_3330_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_dec_ref(v_env_3334_);
lean_dec(v_declHint_3330_);
v___x_3348_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
lean_ctor_set(v___x_3349_, 1, v_c_3346_);
v___x_3350_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = l_Lean_MessageData_note(v___x_3351_);
v___x_3353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3353_, 0, v_msg_3329_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
return v___x_3354_;
}
else
{
lean_object* v_val_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3390_; 
v_val_3355_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3357_ = v___x_3347_;
v_isShared_3358_ = v_isSharedCheck_3390_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_val_3355_);
lean_dec(v___x_3347_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3390_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v_mod_3362_; uint8_t v___x_3363_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = l_Lean_Environment_header(v_env_3334_);
lean_dec_ref(v_env_3334_);
v___x_3361_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3360_);
v_mod_3362_ = lean_array_get(v___x_3359_, v___x_3361_, v_val_3355_);
lean_dec(v_val_3355_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l_Lean_isPrivateName(v_declHint_3330_);
lean_dec(v_declHint_3330_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3364_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_3365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
lean_ctor_set(v___x_3365_, 1, v_c_3346_);
v___x_3366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_3367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = l_Lean_MessageData_ofName(v_mod_3362_);
v___x_3369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_3371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = l_Lean_MessageData_note(v___x_3371_);
v___x_3373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3373_, 0, v_msg_3329_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set_tag(v___x_3357_, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3373_);
v___x_3375_ = v___x_3357_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3377_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
lean_ctor_set(v___x_3378_, 1, v_c_3346_);
v___x_3379_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_3380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = l_Lean_MessageData_ofName(v_mod_3362_);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_3384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3382_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = l_Lean_MessageData_note(v___x_3384_);
v___x_3386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_msg_3329_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set_tag(v___x_3357_, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3386_);
v___x_3388_ = v___x_3357_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3391_; 
lean_dec_ref(v_env_3334_);
lean_dec(v_declHint_3330_);
v___x_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3391_, 0, v_msg_3329_);
return v___x_3391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3392_, lean_object* v_declHint_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3392_, v_declHint_3393_, v___y_3394_);
lean_dec(v___y_3394_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_3397_, lean_object* v_declHint_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3414_; 
v___x_3404_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3397_, v_declHint_3398_, v___y_3402_);
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3414_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3414_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3412_; 
v___x_3409_ = l_Lean_unknownIdentifierMessageTag;
v___x_3410_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
lean_ctor_set(v___x_3410_, 1, v_a_3405_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3410_);
v___x_3412_ = v___x_3407_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_3415_, lean_object* v_declHint_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_3415_, v_declHint_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_ref_3423_, lean_object* v_msg_3424_, lean_object* v_declHint_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v___x_3431_; lean_object* v_a_3432_; lean_object* v___x_3433_; 
v___x_3431_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_3424_, v_declHint_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref(v___x_3431_);
v___x_3433_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3423_, v_a_3432_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_ref_3434_, lean_object* v_msg_3435_, lean_object* v_declHint_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3434_, v_msg_3435_, v_declHint_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v_ref_3434_);
return v_res_3442_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0));
v___x_3445_ = l_Lean_stringToMessageData(v___x_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_3446_, lean_object* v_constName_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v___x_3453_; uint8_t v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3453_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_3454_ = 0;
lean_inc(v_constName_3447_);
v___x_3455_ = l_Lean_MessageData_ofConstName(v_constName_3447_, v___x_3454_);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3453_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3446_, v___x_3458_, v_constName_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_3460_, lean_object* v_constName_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3460_, v_constName_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v_ref_3460_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(lean_object* v_constName_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_ref_3474_; lean_object* v___x_3475_; 
v_ref_3474_ = lean_ctor_get(v___y_3471_, 5);
v___x_3475_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3474_, v_constName_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg___boxed(lean_object* v_constName_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(lean_object* v_constName_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v___x_3489_; lean_object* v_env_3490_; uint8_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3489_ = lean_st_ref_get(v___y_3487_);
v_env_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc_ref(v_env_3490_);
lean_dec(v___x_3489_);
v___x_3491_ = 0;
lean_inc(v_constName_3483_);
v___x_3492_ = l_Lean_Environment_find_x3f(v_env_3490_, v_constName_3483_, v___x_3491_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
return v___x_3493_;
}
else
{
lean_object* v_val_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec(v_constName_3483_);
v_val_3494_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3492_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_val_3494_);
lean_dec(v___x_3492_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set_tag(v___x_3496_, 0);
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_val_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3___boxed(lean_object* v_constName_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(v_constName_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator(lean_object* v_elimName_3509_, uint8_t v_induction_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = lean_box(0);
lean_inc(v_elimName_3509_);
v___x_3517_ = l_Lean_Meta_getElimInfo(v_elimName_3509_, v___x_3516_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref(v___x_3517_);
lean_inc(v_elimName_3509_);
v___x_3519_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(v_elimName_3509_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3521_; lean_object* v___f_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; lean_object* v___x_3525_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref(v___x_3519_);
v___x_3521_ = lean_box(v_induction_3510_);
v___f_3522_ = lean_alloc_closure((void*)(l_Lean_Meta_mkCustomEliminator___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3522_, 0, v_a_3518_);
lean_closure_set(v___f_3522_, 1, v___x_3521_);
lean_closure_set(v___f_3522_, 2, v_elimName_3509_);
v___x_3523_ = l_Lean_ConstantInfo_type(v_a_3520_);
lean_dec(v_a_3520_);
v___x_3524_ = 0;
v___x_3525_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v___x_3523_, v___f_3522_, v___x_3524_, v___x_3524_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
return v___x_3525_;
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v_a_3518_);
lean_dec(v_elimName_3509_);
v_a_3526_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3519_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3519_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec(v_elimName_3509_);
v_a_3534_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3517_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3517_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___boxed(lean_object* v_elimName_3542_, lean_object* v_induction_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
uint8_t v_induction_boxed_3549_; lean_object* v_res_3550_; 
v_induction_boxed_3549_ = lean_unbox(v_induction_3543_);
v_res_3550_ = l_Lean_Meta_mkCustomEliminator(v_elimName_3542_, v_induction_boxed_3549_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(lean_object* v_upperBound_3551_, lean_object* v___x_3552_, lean_object* v_xs_3553_, lean_object* v___x_3554_, lean_object* v_inst_3555_, lean_object* v_R_3556_, lean_object* v_a_3557_, lean_object* v_b_3558_, lean_object* v_c_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v_upperBound_3551_, v___x_3552_, v_xs_3553_, v___x_3554_, v_a_3557_, v_b_3558_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___boxed(lean_object* v_upperBound_3566_, lean_object* v___x_3567_, lean_object* v_xs_3568_, lean_object* v___x_3569_, lean_object* v_inst_3570_, lean_object* v_R_3571_, lean_object* v_a_3572_, lean_object* v_b_3573_, lean_object* v_c_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(v_upperBound_3566_, v___x_3567_, v_xs_3568_, v___x_3569_, v_inst_3570_, v_R_3571_, v_a_3572_, v_b_3573_, v_c_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec_ref(v___x_3569_);
lean_dec_ref(v_xs_3568_);
lean_dec_ref(v___x_3567_);
lean_dec(v_upperBound_3566_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(lean_object* v_upperBound_3581_, lean_object* v___x_3582_, lean_object* v___x_3583_, lean_object* v_xs_3584_, lean_object* v_inst_3585_, lean_object* v_R_3586_, lean_object* v_a_3587_, lean_object* v_b_3588_, lean_object* v_c_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v_upperBound_3581_, v___x_3582_, v___x_3583_, v_xs_3584_, v_a_3587_, v_b_3588_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___boxed(lean_object* v_upperBound_3596_, lean_object* v___x_3597_, lean_object* v___x_3598_, lean_object* v_xs_3599_, lean_object* v_inst_3600_, lean_object* v_R_3601_, lean_object* v_a_3602_, lean_object* v_b_3603_, lean_object* v_c_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(v_upperBound_3596_, v___x_3597_, v___x_3598_, v_xs_3599_, v_inst_3600_, v_R_3601_, v_a_3602_, v_b_3603_, v_c_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v_xs_3599_);
lean_dec_ref(v___x_3598_);
lean_dec(v___x_3597_);
lean_dec(v_upperBound_3596_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(lean_object* v_00_u03b1_3611_, lean_object* v_constName_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___boxed(lean_object* v_00_u03b1_3619_, lean_object* v_constName_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(v_00_u03b1_3619_, v_constName_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_3627_, lean_object* v_ref_3628_, lean_object* v_constName_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3628_, v_constName_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3636_, lean_object* v_ref_3637_, lean_object* v_constName_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(v_00_u03b1_3636_, v_ref_3637_, v_constName_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v_ref_3637_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3645_, lean_object* v_ref_3646_, lean_object* v_msg_3647_, lean_object* v_declHint_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3646_, v_msg_3647_, v_declHint_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3655_, lean_object* v_ref_3656_, lean_object* v_msg_3657_, lean_object* v_declHint_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3655_, v_ref_3656_, v_msg_3657_, v_declHint_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v_ref_3656_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(lean_object* v_msg_3665_, lean_object* v_declHint_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3665_, v_declHint_3666_, v___y_3670_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_3673_, lean_object* v_declHint_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(v_msg_3673_, v_declHint_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(lean_object* v_00_u03b1_3681_, lean_object* v_ref_3682_, lean_object* v_msg_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3682_, v_msg_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3690_, lean_object* v_ref_3691_, lean_object* v_msg_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(v_00_u03b1_3690_, v_ref_3691_, v_msg_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v_ref_3691_);
return v_res_3698_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3699_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0);
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
return v___x_3701_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
v___x_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
return v___x_3703_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
v___x_3705_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
lean_ctor_set(v___x_3705_, 2, v___x_3704_);
lean_ctor_set(v___x_3705_, 3, v___x_3704_);
lean_ctor_set(v___x_3705_, 4, v___x_3704_);
lean_ctor_set(v___x_3705_, 5, v___x_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(lean_object* v_ext_3706_, lean_object* v_b_3707_, uint8_t v_kind_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_currNamespace_3713_; lean_object* v___x_3714_; lean_object* v_env_3715_; lean_object* v_nextMacroScope_3716_; lean_object* v_ngen_3717_; lean_object* v_auxDeclNGen_3718_; lean_object* v_traceState_3719_; lean_object* v_messages_3720_; lean_object* v_infoState_3721_; lean_object* v_snapshotTasks_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3749_; 
v_currNamespace_3713_ = lean_ctor_get(v___y_3710_, 6);
lean_inc(v_currNamespace_3713_);
lean_dec_ref(v___y_3710_);
v___x_3714_ = lean_st_ref_take(v___y_3711_);
v_env_3715_ = lean_ctor_get(v___x_3714_, 0);
v_nextMacroScope_3716_ = lean_ctor_get(v___x_3714_, 1);
v_ngen_3717_ = lean_ctor_get(v___x_3714_, 2);
v_auxDeclNGen_3718_ = lean_ctor_get(v___x_3714_, 3);
v_traceState_3719_ = lean_ctor_get(v___x_3714_, 4);
v_messages_3720_ = lean_ctor_get(v___x_3714_, 6);
v_infoState_3721_ = lean_ctor_get(v___x_3714_, 7);
v_snapshotTasks_3722_ = lean_ctor_get(v___x_3714_, 8);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; 
v_unused_3750_ = lean_ctor_get(v___x_3714_, 5);
lean_dec(v_unused_3750_);
v___x_3724_ = v___x_3714_;
v_isShared_3725_ = v_isSharedCheck_3749_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_snapshotTasks_3722_);
lean_inc(v_infoState_3721_);
lean_inc(v_messages_3720_);
lean_inc(v_traceState_3719_);
lean_inc(v_auxDeclNGen_3718_);
lean_inc(v_ngen_3717_);
lean_inc(v_nextMacroScope_3716_);
lean_inc(v_env_3715_);
lean_dec(v___x_3714_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3749_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3726_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3715_, v_ext_3706_, v_b_3707_, v_kind_3708_, v_currNamespace_3713_);
v___x_3727_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 5, v___x_3727_);
lean_ctor_set(v___x_3724_, 0, v___x_3726_);
v___x_3729_ = v___x_3724_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_nextMacroScope_3716_);
lean_ctor_set(v_reuseFailAlloc_3748_, 2, v_ngen_3717_);
lean_ctor_set(v_reuseFailAlloc_3748_, 3, v_auxDeclNGen_3718_);
lean_ctor_set(v_reuseFailAlloc_3748_, 4, v_traceState_3719_);
lean_ctor_set(v_reuseFailAlloc_3748_, 5, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3748_, 6, v_messages_3720_);
lean_ctor_set(v_reuseFailAlloc_3748_, 7, v_infoState_3721_);
lean_ctor_set(v_reuseFailAlloc_3748_, 8, v_snapshotTasks_3722_);
v___x_3729_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v_mctx_3732_; lean_object* v_zetaDeltaFVarIds_3733_; lean_object* v_postponed_3734_; lean_object* v_diag_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3746_; 
v___x_3730_ = lean_st_ref_set(v___y_3711_, v___x_3729_);
v___x_3731_ = lean_st_ref_take(v___y_3709_);
v_mctx_3732_ = lean_ctor_get(v___x_3731_, 0);
v_zetaDeltaFVarIds_3733_ = lean_ctor_get(v___x_3731_, 2);
v_postponed_3734_ = lean_ctor_get(v___x_3731_, 3);
v_diag_3735_ = lean_ctor_get(v___x_3731_, 4);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; 
v_unused_3747_ = lean_ctor_get(v___x_3731_, 1);
lean_dec(v_unused_3747_);
v___x_3737_ = v___x_3731_;
v_isShared_3738_ = v_isSharedCheck_3746_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_diag_3735_);
lean_inc(v_postponed_3734_);
lean_inc(v_zetaDeltaFVarIds_3733_);
lean_inc(v_mctx_3732_);
lean_dec(v___x_3731_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3746_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3739_; lean_object* v___x_3741_; 
v___x_3739_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 1, v___x_3739_);
v___x_3741_ = v___x_3737_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_mctx_3732_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v_zetaDeltaFVarIds_3733_);
lean_ctor_set(v_reuseFailAlloc_3745_, 3, v_postponed_3734_);
lean_ctor_set(v_reuseFailAlloc_3745_, 4, v_diag_3735_);
v___x_3741_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3742_ = lean_st_ref_set(v___y_3709_, v___x_3741_);
v___x_3743_ = lean_box(0);
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
return v___x_3744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___boxed(lean_object* v_ext_3751_, lean_object* v_b_3752_, lean_object* v_kind_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
uint8_t v_kind_boxed_3758_; lean_object* v_res_3759_; 
v_kind_boxed_3758_ = lean_unbox(v_kind_3753_);
v_res_3759_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v_ext_3751_, v_b_3752_, v_kind_boxed_3758_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec(v___y_3754_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(lean_object* v_00_u03b1_3760_, lean_object* v_00_u03b2_3761_, lean_object* v_00_u03c3_3762_, lean_object* v_ext_3763_, lean_object* v_b_3764_, uint8_t v_kind_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; 
lean_inc_ref(v___y_3768_);
v___x_3771_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v_ext_3763_, v_b_3764_, v_kind_3765_, v___y_3767_, v___y_3768_, v___y_3769_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___boxed(lean_object* v_00_u03b1_3772_, lean_object* v_00_u03b2_3773_, lean_object* v_00_u03c3_3774_, lean_object* v_ext_3775_, lean_object* v_b_3776_, lean_object* v_kind_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
uint8_t v_kind_boxed_3783_; lean_object* v_res_3784_; 
v_kind_boxed_3783_ = lean_unbox(v_kind_3777_);
v_res_3784_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(v_00_u03b1_3772_, v_00_u03b2_3773_, v_00_u03c3_3774_, v_ext_3775_, v_b_3776_, v_kind_boxed_3783_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator(lean_object* v_declName_3785_, uint8_t v_attrKind_3786_, uint8_t v_induction_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l_Lean_Meta_mkCustomEliminator(v_declName_3785_, v_induction_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref(v___x_3793_);
v___x_3795_ = l_Lean_Meta_customEliminatorExt;
lean_inc_ref(v_a_3790_);
v___x_3796_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v___x_3795_, v_a_3794_, v_attrKind_3786_, v_a_3789_, v_a_3790_, v_a_3791_);
return v___x_3796_;
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
v_a_3797_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3793_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3793_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator___boxed(lean_object* v_declName_3805_, lean_object* v_attrKind_3806_, lean_object* v_induction_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_){
_start:
{
uint8_t v_attrKind_boxed_3813_; uint8_t v_induction_boxed_3814_; lean_object* v_res_3815_; 
v_attrKind_boxed_3813_ = lean_unbox(v_attrKind_3806_);
v_induction_boxed_3814_ = lean_unbox(v_induction_3807_);
v_res_3815_ = l_Lean_Meta_addCustomEliminator(v_declName_3805_, v_attrKind_boxed_3813_, v_induction_boxed_3814_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
return v_res_3815_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3822_; uint64_t v___x_3823_; 
v___x_3822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3823_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3822_);
return v___x_3823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3824_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3826_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
lean_ctor_set_uint64(v___x_3826_, sizeof(void*)*1, v___x_3824_);
return v___x_3826_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
return v___x_3829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3831_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
lean_ctor_set(v___x_3831_, 2, v___x_3830_);
lean_ctor_set(v___x_3831_, 3, v___x_3830_);
lean_ctor_set(v___x_3831_, 4, v___x_3830_);
lean_ctor_set(v___x_3831_, 5, v___x_3830_);
return v___x_3831_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
lean_ctor_set(v___x_3833_, 1, v___x_3832_);
lean_ctor_set(v___x_3833_, 2, v___x_3832_);
lean_ctor_set(v___x_3833_, 3, v___x_3832_);
lean_ctor_set(v___x_3833_, 4, v___x_3832_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object* v___x_3834_, lean_object* v___x_3835_, lean_object* v_declName_3836_, lean_object* v_x_3837_, uint8_t v_attrKind_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
uint8_t v___x_3842_; uint8_t v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; size_t v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3842_ = 1;
v___x_3843_ = 0;
v___x_3844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3846_ = lean_unsigned_to_nat(32u);
v___x_3847_ = lean_mk_empty_array_with_capacity(v___x_3846_);
v___x_3848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3849_ = ((size_t)5ULL);
lean_inc_n(v___x_3834_, 2);
v___x_3850_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set(v___x_3850_, 1, v___x_3847_);
lean_ctor_set(v___x_3850_, 2, v___x_3834_);
lean_ctor_set(v___x_3850_, 3, v___x_3834_);
lean_ctor_set_usize(v___x_3850_, 4, v___x_3849_);
v___x_3851_ = lean_box(1);
lean_inc_ref(v___x_3850_);
v___x_3852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3845_);
lean_ctor_set(v___x_3852_, 1, v___x_3850_);
lean_ctor_set(v___x_3852_, 2, v___x_3851_);
v___x_3853_ = lean_mk_empty_array_with_capacity(v___x_3834_);
v___x_3854_ = lean_box(0);
lean_inc(v___x_3834_);
lean_inc(v___x_3835_);
v___x_3855_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3855_, 0, v___x_3844_);
lean_ctor_set(v___x_3855_, 1, v___x_3835_);
lean_ctor_set(v___x_3855_, 2, v___x_3852_);
lean_ctor_set(v___x_3855_, 3, v___x_3853_);
lean_ctor_set(v___x_3855_, 4, v___x_3854_);
lean_ctor_set(v___x_3855_, 5, v___x_3834_);
lean_ctor_set(v___x_3855_, 6, v___x_3854_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*7, v___x_3843_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*7 + 1, v___x_3843_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*7 + 2, v___x_3843_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*7 + 3, v___x_3842_);
lean_inc_n(v___x_3834_, 2);
v___x_3856_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3834_);
lean_ctor_set(v___x_3856_, 1, v___x_3834_);
lean_ctor_set(v___x_3856_, 2, v___x_3834_);
lean_ctor_set(v___x_3856_, 3, v___x_3845_);
lean_ctor_set(v___x_3856_, 4, v___x_3845_);
lean_ctor_set(v___x_3856_, 5, v___x_3845_);
lean_ctor_set(v___x_3856_, 6, v___x_3845_);
lean_ctor_set(v___x_3856_, 7, v___x_3845_);
lean_ctor_set(v___x_3856_, 8, v___x_3845_);
v___x_3857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3856_);
lean_ctor_set(v___x_3859_, 1, v___x_3857_);
lean_ctor_set(v___x_3859_, 2, v___x_3835_);
lean_ctor_set(v___x_3859_, 3, v___x_3850_);
lean_ctor_set(v___x_3859_, 4, v___x_3858_);
v___x_3860_ = lean_st_mk_ref(v___x_3859_);
v___x_3861_ = l_Lean_Meta_addCustomEliminator(v_declName_3836_, v_attrKind_3838_, v___x_3842_, v___x_3855_, v___x_3860_, v___y_3839_, v___y_3840_);
lean_dec_ref(v___x_3855_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3870_; 
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3870_ == 0)
{
lean_object* v_unused_3871_; 
v_unused_3871_ = lean_ctor_get(v___x_3861_, 0);
lean_dec(v_unused_3871_);
v___x_3863_ = v___x_3861_;
v_isShared_3864_ = v_isSharedCheck_3870_;
goto v_resetjp_3862_;
}
else
{
lean_dec(v___x_3861_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3870_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3868_; 
v___x_3865_ = lean_st_ref_get(v___x_3860_);
lean_dec(v___x_3860_);
lean_dec(v___x_3865_);
v___x_3866_ = lean_box(0);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3866_);
v___x_3868_ = v___x_3863_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3866_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
else
{
lean_dec(v___x_3860_);
return v___x_3861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v___x_3872_, lean_object* v___x_3873_, lean_object* v_declName_3874_, lean_object* v_x_3875_, lean_object* v_attrKind_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
uint8_t v_attrKind_boxed_3880_; lean_object* v_res_3881_; 
v_attrKind_boxed_3880_ = lean_unbox(v_attrKind_3876_);
v_res_3881_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_3872_, v___x_3873_, v_declName_3874_, v_x_3875_, v_attrKind_boxed_3880_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v_x_3875_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; lean_object* v_env_3887_; lean_object* v_options_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3886_ = lean_st_ref_get(v___y_3884_);
v_env_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc_ref(v_env_3887_);
lean_dec(v___x_3886_);
v_options_3888_ = lean_ctor_get(v___y_3883_, 2);
v___x_3889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_3890_ = lean_unsigned_to_nat(32u);
v___x_3891_ = lean_mk_empty_array_with_capacity(v___x_3890_);
lean_dec_ref(v___x_3891_);
v___x_3892_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
lean_inc_ref(v_options_3888_);
v___x_3893_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3893_, 0, v_env_3887_);
lean_ctor_set(v___x_3893_, 1, v___x_3889_);
lean_ctor_set(v___x_3893_, 2, v___x_3892_);
lean_ctor_set(v___x_3893_, 3, v_options_3888_);
v___x_3894_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
lean_ctor_set(v___x_3894_, 1, v_msgData_3882_);
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v_ref_3905_; lean_object* v___x_3906_; lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3915_; 
v_ref_3905_ = lean_ctor_get(v___y_3902_, 5);
v___x_3906_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msg_3901_, v___y_3902_, v___y_3903_);
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3909_ = v___x_3906_;
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3906_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
lean_inc(v_ref_3905_);
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v_ref_3905_);
lean_ctor_set(v___x_3911_, 1, v_a_3907_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set_tag(v___x_3909_, 1);
lean_ctor_set(v___x_3909_, 0, v___x_3911_);
v___x_3913_ = v___x_3909_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_3916_, v___y_3917_, v___y_3918_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
return v_res_3920_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3923_ = l_Lean_stringToMessageData(v___x_3922_);
return v___x_3923_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3926_ = l_Lean_stringToMessageData(v___x_3925_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object* v___x_3927_, lean_object* v_decl_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3933_ = l_Lean_MessageData_ofName(v___x_3927_);
v___x_3934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3932_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
v___x_3935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3934_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_3936_, v___y_3929_, v___y_3930_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v___x_3938_, lean_object* v_decl_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_3938_, v_decl_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v_decl_3939_);
return v_res_3943_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3994_ = lean_unsigned_to_nat(2729305610u);
v___x_3995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3996_ = l_Lean_Name_num___override(v___x_3995_, v___x_3994_);
return v___x_3996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3999_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4000_ = l_Lean_Name_str___override(v___x_3999_, v___x_3998_);
return v___x_4000_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4003_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4004_ = l_Lean_Name_str___override(v___x_4003_, v___x_4002_);
return v___x_4004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = lean_unsigned_to_nat(2u);
v___x_4006_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4007_ = l_Lean_Name_num___override(v___x_4006_, v___x_4005_);
return v___x_4007_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4014_ = 0;
v___x_4015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4017_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4018_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
lean_ctor_set(v___x_4018_, 1, v___x_4016_);
lean_ctor_set(v___x_4018_, 2, v___x_4015_);
lean_ctor_set_uint8(v___x_4018_, sizeof(void*)*3, v___x_4014_);
return v___x_4018_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4019_; lean_object* v___f_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___f_4019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___f_4020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4021_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
lean_ctor_set(v___x_4022_, 1, v___f_4020_);
lean_ctor_set(v___x_4022_, 2, v___f_4019_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4025_ = l_Lean_registerBuiltinAttribute(v___x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_4028_, lean_object* v_msg_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_4029_, v___y_4030_, v___y_4031_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_4034_, lean_object* v_msg_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(v_00_u03b1_4034_, v_msg_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4044_ = l_Lean_addBuiltinDocString(v___x_4042_, v___x_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v_a_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object* v___x_4047_, lean_object* v___x_4048_, lean_object* v_declName_4049_, lean_object* v_x_4050_, uint8_t v_attrKind_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
uint8_t v___x_4055_; uint8_t v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; size_t v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4055_ = 0;
v___x_4056_ = 1;
v___x_4057_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4058_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4059_ = lean_unsigned_to_nat(32u);
v___x_4060_ = lean_mk_empty_array_with_capacity(v___x_4059_);
v___x_4061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_4062_ = ((size_t)5ULL);
lean_inc_n(v___x_4047_, 2);
v___x_4063_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4063_, 0, v___x_4061_);
lean_ctor_set(v___x_4063_, 1, v___x_4060_);
lean_ctor_set(v___x_4063_, 2, v___x_4047_);
lean_ctor_set(v___x_4063_, 3, v___x_4047_);
lean_ctor_set_usize(v___x_4063_, 4, v___x_4062_);
v___x_4064_ = lean_box(1);
lean_inc_ref(v___x_4063_);
v___x_4065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4058_);
lean_ctor_set(v___x_4065_, 1, v___x_4063_);
lean_ctor_set(v___x_4065_, 2, v___x_4064_);
v___x_4066_ = lean_mk_empty_array_with_capacity(v___x_4047_);
v___x_4067_ = lean_box(0);
lean_inc(v___x_4047_);
lean_inc(v___x_4048_);
v___x_4068_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4068_, 0, v___x_4057_);
lean_ctor_set(v___x_4068_, 1, v___x_4048_);
lean_ctor_set(v___x_4068_, 2, v___x_4065_);
lean_ctor_set(v___x_4068_, 3, v___x_4066_);
lean_ctor_set(v___x_4068_, 4, v___x_4067_);
lean_ctor_set(v___x_4068_, 5, v___x_4047_);
lean_ctor_set(v___x_4068_, 6, v___x_4067_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*7, v___x_4055_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*7 + 1, v___x_4055_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*7 + 2, v___x_4055_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*7 + 3, v___x_4056_);
lean_inc_n(v___x_4047_, 2);
v___x_4069_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4047_);
lean_ctor_set(v___x_4069_, 1, v___x_4047_);
lean_ctor_set(v___x_4069_, 2, v___x_4047_);
lean_ctor_set(v___x_4069_, 3, v___x_4058_);
lean_ctor_set(v___x_4069_, 4, v___x_4058_);
lean_ctor_set(v___x_4069_, 5, v___x_4058_);
lean_ctor_set(v___x_4069_, 6, v___x_4058_);
lean_ctor_set(v___x_4069_, 7, v___x_4058_);
lean_ctor_set(v___x_4069_, 8, v___x_4058_);
v___x_4070_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4071_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4069_);
lean_ctor_set(v___x_4072_, 1, v___x_4070_);
lean_ctor_set(v___x_4072_, 2, v___x_4048_);
lean_ctor_set(v___x_4072_, 3, v___x_4063_);
lean_ctor_set(v___x_4072_, 4, v___x_4071_);
v___x_4073_ = lean_st_mk_ref(v___x_4072_);
v___x_4074_ = l_Lean_Meta_addCustomEliminator(v_declName_4049_, v_attrKind_4051_, v___x_4055_, v___x_4068_, v___x_4073_, v___y_4052_, v___y_4053_);
lean_dec_ref(v___x_4068_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4083_; 
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4083_ == 0)
{
lean_object* v_unused_4084_; 
v_unused_4084_ = lean_ctor_get(v___x_4074_, 0);
lean_dec(v_unused_4084_);
v___x_4076_ = v___x_4074_;
v_isShared_4077_ = v_isSharedCheck_4083_;
goto v_resetjp_4075_;
}
else
{
lean_dec(v___x_4074_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4083_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4081_; 
v___x_4078_ = lean_st_ref_get(v___x_4073_);
lean_dec(v___x_4073_);
lean_dec(v___x_4078_);
v___x_4079_ = lean_box(0);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4079_);
v___x_4081_ = v___x_4076_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4079_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
else
{
lean_dec(v___x_4073_);
return v___x_4074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v___x_4085_, lean_object* v___x_4086_, lean_object* v_declName_4087_, lean_object* v_x_4088_, lean_object* v_attrKind_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
uint8_t v_attrKind_boxed_4093_; lean_object* v_res_4094_; 
v_attrKind_boxed_4093_ = lean_unbox(v_attrKind_4089_);
v_res_4094_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_4085_, v___x_4086_, v_declName_4087_, v_x_4088_, v_attrKind_boxed_4093_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v_x_4088_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object* v___x_4095_, lean_object* v_decl_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4101_ = l_Lean_MessageData_ofName(v___x_4095_);
v___x_4102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4100_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
v___x_4103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4102_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_4104_, v___y_4097_, v___y_4098_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v___x_4106_, lean_object* v_decl_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_4106_, v_decl_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v_decl_4107_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4144_ = l_Lean_registerBuiltinAttribute(v___x_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4151_ = l_Lean_addBuiltinDocString(v___x_4149_, v___x_4150_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v_a_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg(lean_object* v_a_4154_){
_start:
{
lean_object* v___x_4156_; lean_object* v_env_4157_; lean_object* v___x_4158_; lean_object* v_ext_4159_; lean_object* v_toEnvExtension_4160_; lean_object* v_asyncMode_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4156_ = lean_st_ref_get(v_a_4154_);
v_env_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc_ref(v_env_4157_);
lean_dec(v___x_4156_);
v___x_4158_ = l_Lean_Meta_customEliminatorExt;
v_ext_4159_ = lean_ctor_get(v___x_4158_, 1);
lean_inc_ref(v_ext_4159_);
v_toEnvExtension_4160_ = lean_ctor_get(v_ext_4159_, 0);
lean_inc_ref(v_toEnvExtension_4160_);
lean_dec_ref(v_ext_4159_);
v_asyncMode_4161_ = lean_ctor_get(v_toEnvExtension_4160_, 2);
lean_inc(v_asyncMode_4161_);
lean_dec_ref(v_toEnvExtension_4160_);
v___x_4162_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
v___x_4163_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4162_, v___x_4158_, v_env_4157_, v_asyncMode_4161_);
lean_dec(v_asyncMode_4161_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg___boxed(lean_object* v_a_4165_, lean_object* v_a_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_4165_);
lean_dec(v_a_4165_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators(lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_4169_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___boxed(lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Meta_getCustomEliminators(v_a_4172_, v_a_4173_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_a_4176_, lean_object* v_x_4177_){
_start:
{
if (lean_obj_tag(v_x_4177_) == 0)
{
lean_object* v___x_4178_; 
v___x_4178_ = lean_box(0);
return v___x_4178_;
}
else
{
lean_object* v_key_4179_; lean_object* v_value_4180_; lean_object* v_tail_4181_; lean_object* v_fst_4182_; lean_object* v_snd_4183_; lean_object* v_fst_4184_; lean_object* v_snd_4185_; uint8_t v___x_4194_; 
v_key_4179_ = lean_ctor_get(v_x_4177_, 0);
v_value_4180_ = lean_ctor_get(v_x_4177_, 1);
v_tail_4181_ = lean_ctor_get(v_x_4177_, 2);
v_fst_4182_ = lean_ctor_get(v_key_4179_, 0);
v_snd_4183_ = lean_ctor_get(v_key_4179_, 1);
v_fst_4184_ = lean_ctor_get(v_a_4176_, 0);
v_snd_4185_ = lean_ctor_get(v_a_4176_, 1);
v___x_4194_ = lean_unbox(v_fst_4182_);
if (v___x_4194_ == 0)
{
uint8_t v___x_4195_; 
v___x_4195_ = lean_unbox(v_fst_4184_);
if (v___x_4195_ == 0)
{
goto v___jp_4186_;
}
else
{
v_x_4177_ = v_tail_4181_;
goto _start;
}
}
else
{
uint8_t v___x_4197_; 
v___x_4197_ = lean_unbox(v_fst_4184_);
if (v___x_4197_ == 0)
{
v_x_4177_ = v_tail_4181_;
goto _start;
}
else
{
goto v___jp_4186_;
}
}
v___jp_4186_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; 
v___x_4187_ = lean_array_get_size(v_snd_4183_);
v___x_4188_ = lean_array_get_size(v_snd_4185_);
v___x_4189_ = lean_nat_dec_eq(v___x_4187_, v___x_4188_);
if (v___x_4189_ == 0)
{
v_x_4177_ = v_tail_4181_;
goto _start;
}
else
{
uint8_t v___x_4191_; 
v___x_4191_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4183_, v_snd_4185_, v___x_4187_);
if (v___x_4191_ == 0)
{
v_x_4177_ = v_tail_4181_;
goto _start;
}
else
{
lean_object* v___x_4193_; 
lean_inc(v_value_4180_);
v___x_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4193_, 0, v_value_4180_);
return v___x_4193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_4199_, lean_object* v_x_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4199_, v_x_4200_);
lean_dec(v_x_4200_);
lean_dec_ref(v_a_4199_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(lean_object* v_m_4202_, lean_object* v_a_4203_){
_start:
{
lean_object* v_buckets_4204_; lean_object* v_fst_4205_; lean_object* v_snd_4206_; lean_object* v___x_4207_; uint64_t v___y_4209_; uint64_t v___y_4210_; uint64_t v___y_4226_; uint8_t v___x_4238_; 
v_buckets_4204_ = lean_ctor_get(v_m_4202_, 1);
v_fst_4205_ = lean_ctor_get(v_a_4203_, 0);
v_snd_4206_ = lean_ctor_get(v_a_4203_, 1);
v___x_4207_ = lean_array_get_size(v_buckets_4204_);
v___x_4238_ = lean_unbox(v_fst_4205_);
if (v___x_4238_ == 0)
{
uint64_t v___x_4239_; 
v___x_4239_ = 13ULL;
v___y_4226_ = v___x_4239_;
goto v___jp_4225_;
}
else
{
uint64_t v___x_4240_; 
v___x_4240_ = 11ULL;
v___y_4226_ = v___x_4240_;
goto v___jp_4225_;
}
v___jp_4208_:
{
uint64_t v___x_4211_; uint64_t v___x_4212_; uint64_t v___x_4213_; uint64_t v_fold_4214_; uint64_t v___x_4215_; uint64_t v___x_4216_; uint64_t v___x_4217_; size_t v___x_4218_; size_t v___x_4219_; size_t v___x_4220_; size_t v___x_4221_; size_t v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4211_ = lean_uint64_mix_hash(v___y_4209_, v___y_4210_);
v___x_4212_ = 32ULL;
v___x_4213_ = lean_uint64_shift_right(v___x_4211_, v___x_4212_);
v_fold_4214_ = lean_uint64_xor(v___x_4211_, v___x_4213_);
v___x_4215_ = 16ULL;
v___x_4216_ = lean_uint64_shift_right(v_fold_4214_, v___x_4215_);
v___x_4217_ = lean_uint64_xor(v_fold_4214_, v___x_4216_);
v___x_4218_ = lean_uint64_to_usize(v___x_4217_);
v___x_4219_ = lean_usize_of_nat(v___x_4207_);
v___x_4220_ = ((size_t)1ULL);
v___x_4221_ = lean_usize_sub(v___x_4219_, v___x_4220_);
v___x_4222_ = lean_usize_land(v___x_4218_, v___x_4221_);
v___x_4223_ = lean_array_uget_borrowed(v_buckets_4204_, v___x_4222_);
v___x_4224_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4203_, v___x_4223_);
return v___x_4224_;
}
v___jp_4225_:
{
uint64_t v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; 
v___x_4227_ = 7ULL;
v___x_4228_ = lean_unsigned_to_nat(0u);
v___x_4229_ = lean_array_get_size(v_snd_4206_);
v___x_4230_ = lean_nat_dec_lt(v___x_4228_, v___x_4229_);
if (v___x_4230_ == 0)
{
v___y_4209_ = v___y_4226_;
v___y_4210_ = v___x_4227_;
goto v___jp_4208_;
}
else
{
uint8_t v___x_4231_; 
v___x_4231_ = lean_nat_dec_le(v___x_4229_, v___x_4229_);
if (v___x_4231_ == 0)
{
if (v___x_4230_ == 0)
{
v___y_4209_ = v___y_4226_;
v___y_4210_ = v___x_4227_;
goto v___jp_4208_;
}
else
{
size_t v___x_4232_; size_t v___x_4233_; uint64_t v___x_4234_; 
v___x_4232_ = ((size_t)0ULL);
v___x_4233_ = lean_usize_of_nat(v___x_4229_);
v___x_4234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4206_, v___x_4232_, v___x_4233_, v___x_4227_);
v___y_4209_ = v___y_4226_;
v___y_4210_ = v___x_4234_;
goto v___jp_4208_;
}
}
else
{
size_t v___x_4235_; size_t v___x_4236_; uint64_t v___x_4237_; 
v___x_4235_ = ((size_t)0ULL);
v___x_4236_ = lean_usize_of_nat(v___x_4229_);
v___x_4237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4206_, v___x_4235_, v___x_4236_, v___x_4227_);
v___y_4209_ = v___y_4226_;
v___y_4210_ = v___x_4237_;
goto v___jp_4208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_m_4241_, lean_object* v_a_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_4241_, v_a_4242_);
lean_dec_ref(v_a_4242_);
lean_dec_ref(v_m_4241_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_4244_, lean_object* v_vals_4245_, lean_object* v_i_4246_, lean_object* v_k_4247_){
_start:
{
lean_object* v___x_4252_; uint8_t v___x_4253_; 
v___x_4252_ = lean_array_get_size(v_keys_4244_);
v___x_4253_ = lean_nat_dec_lt(v_i_4246_, v___x_4252_);
if (v___x_4253_ == 0)
{
lean_object* v___x_4254_; 
lean_dec(v_i_4246_);
v___x_4254_ = lean_box(0);
return v___x_4254_;
}
else
{
lean_object* v_fst_4255_; lean_object* v_snd_4256_; lean_object* v_k_x27_4257_; lean_object* v_fst_4258_; lean_object* v_snd_4259_; uint8_t v___y_4261_; uint8_t v___x_4268_; 
v_fst_4255_ = lean_ctor_get(v_k_4247_, 0);
v_snd_4256_ = lean_ctor_get(v_k_4247_, 1);
v_k_x27_4257_ = lean_array_fget_borrowed(v_keys_4244_, v_i_4246_);
v_fst_4258_ = lean_ctor_get(v_k_x27_4257_, 0);
v_snd_4259_ = lean_ctor_get(v_k_x27_4257_, 1);
v___x_4268_ = lean_unbox(v_fst_4255_);
if (v___x_4268_ == 0)
{
uint8_t v___x_4269_; 
v___x_4269_ = lean_unbox(v_fst_4258_);
if (v___x_4269_ == 0)
{
v___y_4261_ = v___x_4253_;
goto v___jp_4260_;
}
else
{
goto v___jp_4248_;
}
}
else
{
uint8_t v___x_4270_; 
v___x_4270_ = lean_unbox(v_fst_4258_);
v___y_4261_ = v___x_4270_;
goto v___jp_4260_;
}
v___jp_4260_:
{
if (v___y_4261_ == 0)
{
goto v___jp_4248_;
}
else
{
lean_object* v___x_4262_; lean_object* v___x_4263_; uint8_t v___x_4264_; 
v___x_4262_ = lean_array_get_size(v_snd_4256_);
v___x_4263_ = lean_array_get_size(v_snd_4259_);
v___x_4264_ = lean_nat_dec_eq(v___x_4262_, v___x_4263_);
if (v___x_4264_ == 0)
{
goto v___jp_4248_;
}
else
{
uint8_t v___x_4265_; 
v___x_4265_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4256_, v_snd_4259_, v___x_4262_);
if (v___x_4265_ == 0)
{
goto v___jp_4248_;
}
else
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4266_ = lean_array_fget_borrowed(v_vals_4245_, v_i_4246_);
lean_dec(v_i_4246_);
lean_inc(v___x_4266_);
v___x_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4266_);
return v___x_4267_;
}
}
}
}
}
v___jp_4248_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = lean_unsigned_to_nat(1u);
v___x_4250_ = lean_nat_add(v_i_4246_, v___x_4249_);
lean_dec(v_i_4246_);
v_i_4246_ = v___x_4250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_4271_, lean_object* v_vals_4272_, lean_object* v_i_4273_, lean_object* v_k_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_4271_, v_vals_4272_, v_i_4273_, v_k_4274_);
lean_dec_ref(v_k_4274_);
lean_dec_ref(v_vals_4272_);
lean_dec_ref(v_keys_4271_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_x_4276_, size_t v_x_4277_, lean_object* v_x_4278_){
_start:
{
if (lean_obj_tag(v_x_4276_) == 0)
{
lean_object* v_es_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4314_; 
v_es_4279_ = lean_ctor_get(v_x_4276_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v_x_4276_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4281_ = v_x_4276_;
v_isShared_4282_ = v_isSharedCheck_4314_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_es_4279_);
lean_dec(v_x_4276_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4314_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4283_; size_t v___x_4284_; size_t v___x_4285_; size_t v___x_4286_; lean_object* v_j_4287_; lean_object* v___x_4288_; 
v___x_4283_ = lean_box(2);
v___x_4284_ = ((size_t)5ULL);
v___x_4285_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_4286_ = lean_usize_land(v_x_4277_, v___x_4285_);
v_j_4287_ = lean_usize_to_nat(v___x_4286_);
v___x_4288_ = lean_array_get(v___x_4283_, v_es_4279_, v_j_4287_);
lean_dec(v_j_4287_);
lean_dec_ref(v_es_4279_);
switch(lean_obj_tag(v___x_4288_))
{
case 0:
{
lean_object* v_key_4289_; lean_object* v_val_4290_; lean_object* v_fst_4291_; lean_object* v_snd_4292_; lean_object* v_fst_4293_; lean_object* v_snd_4294_; uint8_t v___x_4305_; 
v_key_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_key_4289_);
v_val_4290_ = lean_ctor_get(v___x_4288_, 1);
lean_inc(v_val_4290_);
lean_dec_ref(v___x_4288_);
v_fst_4291_ = lean_ctor_get(v_x_4278_, 0);
v_snd_4292_ = lean_ctor_get(v_x_4278_, 1);
v_fst_4293_ = lean_ctor_get(v_key_4289_, 0);
lean_inc(v_fst_4293_);
v_snd_4294_ = lean_ctor_get(v_key_4289_, 1);
lean_inc(v_snd_4294_);
lean_dec(v_key_4289_);
v___x_4305_ = lean_unbox(v_fst_4291_);
if (v___x_4305_ == 0)
{
uint8_t v___x_4306_; 
v___x_4306_ = lean_unbox(v_fst_4293_);
lean_dec(v_fst_4293_);
if (v___x_4306_ == 0)
{
goto v___jp_4295_;
}
else
{
lean_object* v___x_4307_; 
lean_dec(v_snd_4294_);
lean_dec(v_val_4290_);
lean_del_object(v___x_4281_);
v___x_4307_ = lean_box(0);
return v___x_4307_;
}
}
else
{
uint8_t v___x_4308_; 
v___x_4308_ = lean_unbox(v_fst_4293_);
lean_dec(v_fst_4293_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4309_; 
lean_dec(v_snd_4294_);
lean_dec(v_val_4290_);
lean_del_object(v___x_4281_);
v___x_4309_ = lean_box(0);
return v___x_4309_;
}
else
{
goto v___jp_4295_;
}
}
v___jp_4295_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; 
v___x_4296_ = lean_array_get_size(v_snd_4292_);
v___x_4297_ = lean_array_get_size(v_snd_4294_);
v___x_4298_ = lean_nat_dec_eq(v___x_4296_, v___x_4297_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; 
lean_dec(v_snd_4294_);
lean_dec(v_val_4290_);
lean_del_object(v___x_4281_);
v___x_4299_ = lean_box(0);
return v___x_4299_;
}
else
{
uint8_t v___x_4300_; 
v___x_4300_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4292_, v_snd_4294_, v___x_4296_);
lean_dec(v_snd_4294_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; 
lean_dec(v_val_4290_);
lean_del_object(v___x_4281_);
v___x_4301_ = lean_box(0);
return v___x_4301_;
}
else
{
lean_object* v___x_4303_; 
if (v_isShared_4282_ == 0)
{
lean_ctor_set_tag(v___x_4281_, 1);
lean_ctor_set(v___x_4281_, 0, v_val_4290_);
v___x_4303_ = v___x_4281_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_val_4290_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
}
case 1:
{
lean_object* v_node_4310_; size_t v___x_4311_; 
lean_del_object(v___x_4281_);
v_node_4310_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_node_4310_);
lean_dec_ref(v___x_4288_);
v___x_4311_ = lean_usize_shift_right(v_x_4277_, v___x_4284_);
v_x_4276_ = v_node_4310_;
v_x_4277_ = v___x_4311_;
goto _start;
}
default: 
{
lean_object* v___x_4313_; 
lean_del_object(v___x_4281_);
v___x_4313_ = lean_box(0);
return v___x_4313_;
}
}
}
}
else
{
lean_object* v_ks_4315_; lean_object* v_vs_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v_ks_4315_ = lean_ctor_get(v_x_4276_, 0);
lean_inc_ref(v_ks_4315_);
v_vs_4316_ = lean_ctor_get(v_x_4276_, 1);
lean_inc_ref(v_vs_4316_);
lean_dec_ref(v_x_4276_);
v___x_4317_ = lean_unsigned_to_nat(0u);
v___x_4318_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_ks_4315_, v_vs_4316_, v___x_4317_, v_x_4278_);
lean_dec_ref(v_vs_4316_);
lean_dec_ref(v_ks_4315_);
return v___x_4318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_4319_, lean_object* v_x_4320_, lean_object* v_x_4321_){
_start:
{
size_t v_x_2279__boxed_4322_; lean_object* v_res_4323_; 
v_x_2279__boxed_4322_ = lean_unbox_usize(v_x_4320_);
lean_dec(v_x_4320_);
v_res_4323_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4319_, v_x_2279__boxed_4322_, v_x_4321_);
lean_dec_ref(v_x_4321_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(lean_object* v_x_4324_, lean_object* v_x_4325_){
_start:
{
uint64_t v___y_4327_; uint64_t v___y_4328_; lean_object* v_fst_4332_; lean_object* v_snd_4333_; uint64_t v___y_4335_; uint8_t v___x_4347_; 
v_fst_4332_ = lean_ctor_get(v_x_4325_, 0);
v_snd_4333_ = lean_ctor_get(v_x_4325_, 1);
v___x_4347_ = lean_unbox(v_fst_4332_);
if (v___x_4347_ == 0)
{
uint64_t v___x_4348_; 
v___x_4348_ = 13ULL;
v___y_4335_ = v___x_4348_;
goto v___jp_4334_;
}
else
{
uint64_t v___x_4349_; 
v___x_4349_ = 11ULL;
v___y_4335_ = v___x_4349_;
goto v___jp_4334_;
}
v___jp_4326_:
{
uint64_t v___x_4329_; size_t v___x_4330_; lean_object* v___x_4331_; 
v___x_4329_ = lean_uint64_mix_hash(v___y_4327_, v___y_4328_);
v___x_4330_ = lean_uint64_to_usize(v___x_4329_);
v___x_4331_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4324_, v___x_4330_, v_x_4325_);
return v___x_4331_;
}
v___jp_4334_:
{
uint64_t v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4336_ = 7ULL;
v___x_4337_ = lean_unsigned_to_nat(0u);
v___x_4338_ = lean_array_get_size(v_snd_4333_);
v___x_4339_ = lean_nat_dec_lt(v___x_4337_, v___x_4338_);
if (v___x_4339_ == 0)
{
v___y_4327_ = v___y_4335_;
v___y_4328_ = v___x_4336_;
goto v___jp_4326_;
}
else
{
uint8_t v___x_4340_; 
v___x_4340_ = lean_nat_dec_le(v___x_4338_, v___x_4338_);
if (v___x_4340_ == 0)
{
if (v___x_4339_ == 0)
{
v___y_4327_ = v___y_4335_;
v___y_4328_ = v___x_4336_;
goto v___jp_4326_;
}
else
{
size_t v___x_4341_; size_t v___x_4342_; uint64_t v___x_4343_; 
v___x_4341_ = ((size_t)0ULL);
v___x_4342_ = lean_usize_of_nat(v___x_4338_);
v___x_4343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4333_, v___x_4341_, v___x_4342_, v___x_4336_);
v___y_4327_ = v___y_4335_;
v___y_4328_ = v___x_4343_;
goto v___jp_4326_;
}
}
else
{
size_t v___x_4344_; size_t v___x_4345_; uint64_t v___x_4346_; 
v___x_4344_ = ((size_t)0ULL);
v___x_4345_ = lean_usize_of_nat(v___x_4338_);
v___x_4346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4333_, v___x_4344_, v___x_4345_, v___x_4336_);
v___y_4327_ = v___y_4335_;
v___y_4328_ = v___x_4346_;
goto v___jp_4326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_4350_, lean_object* v_x_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_4350_, v_x_4351_);
lean_dec_ref(v_x_4351_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(lean_object* v_x_4353_, lean_object* v_x_4354_){
_start:
{
uint8_t v_stage_u2081_4355_; 
v_stage_u2081_4355_ = lean_ctor_get_uint8(v_x_4353_, sizeof(void*)*2);
if (v_stage_u2081_4355_ == 0)
{
lean_object* v_map_u2081_4356_; lean_object* v_map_u2082_4357_; lean_object* v___x_4358_; 
v_map_u2081_4356_ = lean_ctor_get(v_x_4353_, 0);
lean_inc_ref(v_map_u2081_4356_);
v_map_u2082_4357_ = lean_ctor_get(v_x_4353_, 1);
lean_inc_ref(v_map_u2082_4357_);
lean_dec_ref(v_x_4353_);
v___x_4358_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_map_u2082_4357_, v_x_4354_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v___x_4359_; 
v___x_4359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_4356_, v_x_4354_);
lean_dec_ref(v_map_u2081_4356_);
return v___x_4359_;
}
else
{
lean_dec_ref(v_map_u2081_4356_);
return v___x_4358_;
}
}
else
{
lean_object* v_map_u2081_4360_; lean_object* v___x_4361_; 
v_map_u2081_4360_ = lean_ctor_get(v_x_4353_, 0);
lean_inc_ref(v_map_u2081_4360_);
lean_dec_ref(v_x_4353_);
v___x_4361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_4360_, v_x_4354_);
lean_dec_ref(v_map_u2081_4360_);
return v___x_4361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg___boxed(lean_object* v_x_4362_, lean_object* v_x_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v_x_4362_, v_x_4363_);
lean_dec_ref(v_x_4363_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(lean_object* v_as_4367_, size_t v_sz_4368_, size_t v_i_4369_, lean_object* v_b_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
uint8_t v___x_4376_; 
v___x_4376_ = lean_usize_dec_lt(v_i_4369_, v_sz_4368_);
if (v___x_4376_ == 0)
{
lean_object* v___x_4377_; 
v___x_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4377_, 0, v_b_4370_);
return v___x_4377_;
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4379_; 
v_a_4378_ = lean_array_uget_borrowed(v_as_4367_, v_i_4369_);
lean_inc(v___y_4374_);
lean_inc_ref(v___y_4373_);
lean_inc(v___y_4372_);
lean_inc_ref(v___y_4371_);
lean_inc(v_a_4378_);
v___x_4379_ = lean_infer_type(v_a_4378_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4381_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref(v___x_4379_);
v___x_4381_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_a_4380_, v___y_4372_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4410_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4384_ = v___x_4381_;
v_isShared_4385_ = v_isSharedCheck_4410_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4381_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4410_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v_snd_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4408_; 
v_snd_4386_ = lean_ctor_get(v_b_4370_, 1);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_b_4370_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; 
v_unused_4409_ = lean_ctor_get(v_b_4370_, 0);
lean_dec(v_unused_4409_);
v___x_4388_ = v_b_4370_;
v_isShared_4389_ = v_isSharedCheck_4408_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_snd_4386_);
lean_dec(v_b_4370_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4408_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = l_Lean_Expr_headBeta(v_a_4382_);
v___x_4391_ = l_Lean_Expr_getAppFn(v___x_4390_);
lean_dec_ref(v___x_4390_);
if (lean_obj_tag(v___x_4391_) == 4)
{
lean_object* v_declName_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4396_; 
lean_del_object(v___x_4384_);
v_declName_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_declName_4392_);
lean_dec_ref(v___x_4391_);
v___x_4393_ = lean_box(0);
v___x_4394_ = lean_array_push(v_snd_4386_, v_declName_4392_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 1, v___x_4394_);
lean_ctor_set(v___x_4388_, 0, v___x_4393_);
v___x_4396_ = v___x_4388_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4393_);
lean_ctor_set(v_reuseFailAlloc_4400_, 1, v___x_4394_);
v___x_4396_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
size_t v___x_4397_; size_t v___x_4398_; 
v___x_4397_ = ((size_t)1ULL);
v___x_4398_ = lean_usize_add(v_i_4369_, v___x_4397_);
v_i_4369_ = v___x_4398_;
v_b_4370_ = v___x_4396_;
goto _start;
}
}
else
{
lean_object* v___x_4401_; lean_object* v___x_4403_; 
lean_dec_ref(v___x_4391_);
v___x_4401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0));
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v___x_4401_);
v___x_4403_ = v___x_4388_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4401_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_snd_4386_);
v___x_4403_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4405_; 
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 0, v___x_4403_);
v___x_4405_ = v___x_4384_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4403_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec_ref(v_b_4370_);
v_a_4411_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4381_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4381_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec_ref(v_b_4370_);
v_a_4419_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4379_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4379_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___boxed(lean_object* v_as_4427_, lean_object* v_sz_4428_, lean_object* v_i_4429_, lean_object* v_b_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
size_t v_sz_boxed_4436_; size_t v_i_boxed_4437_; lean_object* v_res_4438_; 
v_sz_boxed_4436_ = lean_unbox_usize(v_sz_4428_);
lean_dec(v_sz_4428_);
v_i_boxed_4437_ = lean_unbox_usize(v_i_4429_);
lean_dec(v_i_4429_);
v_res_4438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_as_4427_, v_sz_boxed_4436_, v_i_boxed_4437_, v_b_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec_ref(v_as_4427_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f(lean_object* v_targets_4442_, uint8_t v_induction_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v___x_4449_; size_t v_sz_4450_; size_t v___x_4451_; lean_object* v___x_4452_; 
v___x_4449_ = ((lean_object*)(l_Lean_Meta_getCustomEliminator_x3f___closed__0));
v_sz_4450_ = lean_array_size(v_targets_4442_);
v___x_4451_ = ((size_t)0ULL);
v___x_4452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_targets_4442_, v_sz_4450_, v___x_4451_, v___x_4449_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4484_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4455_ = v___x_4452_;
v_isShared_4456_ = v_isSharedCheck_4484_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4452_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4484_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v_fst_4457_; 
v_fst_4457_ = lean_ctor_get(v_a_4453_, 0);
if (lean_obj_tag(v_fst_4457_) == 0)
{
lean_object* v_snd_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4478_; 
v_snd_4458_ = lean_ctor_get(v_a_4453_, 1);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_a_4453_);
if (v_isSharedCheck_4478_ == 0)
{
lean_object* v_unused_4479_; 
v_unused_4479_ = lean_ctor_get(v_a_4453_, 0);
lean_dec(v_unused_4479_);
v___x_4460_ = v_a_4453_;
v_isShared_4461_ = v_isSharedCheck_4478_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_snd_4458_);
lean_dec(v_a_4453_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4478_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4462_; lean_object* v_env_4463_; lean_object* v___x_4464_; lean_object* v_ext_4465_; lean_object* v_toEnvExtension_4466_; lean_object* v_asyncMode_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4472_; 
v___x_4462_ = lean_st_ref_get(v_a_4447_);
v_env_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc_ref(v_env_4463_);
lean_dec(v___x_4462_);
v___x_4464_ = l_Lean_Meta_customEliminatorExt;
v_ext_4465_ = lean_ctor_get(v___x_4464_, 1);
lean_inc_ref(v_ext_4465_);
v_toEnvExtension_4466_ = lean_ctor_get(v_ext_4465_, 0);
lean_inc_ref(v_toEnvExtension_4466_);
lean_dec_ref(v_ext_4465_);
v_asyncMode_4467_ = lean_ctor_get(v_toEnvExtension_4466_, 2);
lean_inc(v_asyncMode_4467_);
lean_dec_ref(v_toEnvExtension_4466_);
v___x_4468_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
v___x_4469_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4468_, v___x_4464_, v_env_4463_, v_asyncMode_4467_);
lean_dec(v_asyncMode_4467_);
v___x_4470_ = lean_box(v_induction_4443_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___x_4470_);
v___x_4472_ = v___x_4460_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4470_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_snd_4458_);
v___x_4472_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4473_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v___x_4469_, v___x_4472_);
lean_dec_ref(v___x_4472_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4473_);
v___x_4475_ = v___x_4455_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
else
{
lean_object* v_val_4480_; lean_object* v___x_4482_; 
lean_inc_ref(v_fst_4457_);
lean_dec(v_a_4453_);
v_val_4480_ = lean_ctor_get(v_fst_4457_, 0);
lean_inc(v_val_4480_);
lean_dec_ref(v_fst_4457_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v_val_4480_);
v___x_4482_ = v___x_4455_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_val_4480_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
v_a_4485_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4452_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4452_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f___boxed(lean_object* v_targets_4493_, lean_object* v_induction_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_){
_start:
{
uint8_t v_induction_boxed_4500_; lean_object* v_res_4501_; 
v_induction_boxed_4500_ = lean_unbox(v_induction_4494_);
v_res_4501_ = l_Lean_Meta_getCustomEliminator_x3f(v_targets_4493_, v_induction_boxed_4500_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
lean_dec(v_a_4498_);
lean_dec_ref(v_a_4497_);
lean_dec(v_a_4496_);
lean_dec_ref(v_a_4495_);
lean_dec_ref(v_targets_4493_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(lean_object* v_00_u03b2_4502_, lean_object* v_x_4503_, lean_object* v_x_4504_){
_start:
{
lean_object* v___x_4505_; 
v___x_4505_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v_x_4503_, v_x_4504_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___boxed(lean_object* v_00_u03b2_4506_, lean_object* v_x_4507_, lean_object* v_x_4508_){
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(v_00_u03b2_4506_, v_x_4507_, v_x_4508_);
lean_dec_ref(v_x_4508_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(lean_object* v_00_u03b2_4510_, lean_object* v_x_4511_, lean_object* v_x_4512_){
_start:
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_4511_, v_x_4512_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4514_, lean_object* v_x_4515_, lean_object* v_x_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(v_00_u03b2_4514_, v_x_4515_, v_x_4516_);
lean_dec_ref(v_x_4516_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(lean_object* v_00_u03b2_4518_, lean_object* v_m_4519_, lean_object* v_a_4520_){
_start:
{
lean_object* v___x_4521_; 
v___x_4521_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_4519_, v_a_4520_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4522_, lean_object* v_m_4523_, lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(v_00_u03b2_4522_, v_m_4523_, v_a_4524_);
lean_dec_ref(v_a_4524_);
lean_dec_ref(v_m_4523_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_4526_, lean_object* v_x_4527_, size_t v_x_4528_, lean_object* v_x_4529_){
_start:
{
lean_object* v___x_4530_; 
v___x_4530_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4527_, v_x_4528_, v_x_4529_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4531_, lean_object* v_x_4532_, lean_object* v_x_4533_, lean_object* v_x_4534_){
_start:
{
size_t v_x_2665__boxed_4535_; lean_object* v_res_4536_; 
v_x_2665__boxed_4535_ = lean_unbox_usize(v_x_4533_);
lean_dec(v_x_4533_);
v_res_4536_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(v_00_u03b2_4531_, v_x_4532_, v_x_2665__boxed_4535_, v_x_4534_);
lean_dec_ref(v_x_4534_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4537_, lean_object* v_a_4538_, lean_object* v_x_4539_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4538_, v_x_4539_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4541_, lean_object* v_a_4542_, lean_object* v_x_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(v_00_u03b2_4541_, v_a_4542_, v_x_4543_);
lean_dec(v_x_4543_);
lean_dec_ref(v_a_4542_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4545_, lean_object* v_keys_4546_, lean_object* v_vals_4547_, lean_object* v_heq_4548_, lean_object* v_i_4549_, lean_object* v_k_4550_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_4546_, v_vals_4547_, v_i_4549_, v_k_4550_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4552_, lean_object* v_keys_4553_, lean_object* v_vals_4554_, lean_object* v_heq_4555_, lean_object* v_i_4556_, lean_object* v_k_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(v_00_u03b2_4552_, v_keys_4553_, v_vals_4554_, v_heq_4555_, v_i_4556_, v_k_4557_);
lean_dec_ref(v_k_4557_);
lean_dec_ref(v_vals_4554_);
lean_dec_ref(v_keys_4553_);
return v_res_4558_;
}
}
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
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
