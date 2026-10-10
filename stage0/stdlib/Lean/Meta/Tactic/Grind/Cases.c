// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Cases
// Imports: public import Lean.Meta.Tactic.Cases public import Lean.Meta.Tactic.Grind.Extension
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_NameSet_ofList(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assertExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedCasesEntry_default = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedCasesEntry = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Empty"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10_value),LEAN_SCALAR_PTR_LITERAL(145, 208, 51, 224, 197, 14, 63, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isBuiltinEagerCases___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_isEagerSplit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isEagerSplit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isSplit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_validateCasesAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid `[grind cases]`, `"};
static const lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_validateCasesAttr___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_validateCasesAttr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__1;
static const lean_string_object l_Lean_Meta_Grind_validateCasesAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` is not an inductive datatype or an alias for one"};
static const lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_validateCasesAttr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_validateCasesAttr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__3;
static const lean_string_object l_Lean_Meta_Grind_validateCasesAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "invalid `[grind cases eager]`, `"};
static const lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_validateCasesAttr___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_validateCasesAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__5;
static const lean_string_object l_Lean_Meta_Grind_validateCasesAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` is not a non-recursive inductive datatype or an alias for one"};
static const lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_validateCasesAttr___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_validateCasesAttr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1;
static const lean_string_object l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "` is marked as a built-in case-split for `grind` and cannot be erased"};
static const lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(168, 230, 231, 67, 23, 65, 31, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "(non-recursive) inductive type expected at "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unexpected recursor type"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_cases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_cases___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_cases___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_cases___lam__0___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_cases___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__21;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_cases___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Meta_Grind_cases___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_cases___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Meta_Grind_cases___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_cases___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_Grind_cases___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_cases___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_Grind_cases___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17));
v___x_43_ = l_Lean_NameSet_ofList(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18, &l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18);
return v___x_44_;
}
}
uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object* v_declName_45_){
_start:
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
v___x_47_ = l_Lean_NameSet_contains(v___x_46_, v_declName_45_);
return v___x_47_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isBuiltinEagerCases_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_45_ = stack[0].m_obj;
uint8_t v_res_48_;
v_res_48_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_45_);
stack->m_num = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isBuiltinEagerCases___boxed(lean_object* v_declName_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_49_);
lean_dec(v_declName_49_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_52_, lean_object* v_i_53_, lean_object* v_k_54_){
_start:
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = lean_array_get_size(v_keys_52_);
v___x_56_ = lean_nat_dec_lt(v_i_53_, v___x_55_);
if (v___x_56_ == 0)
{
lean_dec(v_i_53_);
return v___x_56_;
}
else
{
lean_object* v_k_x27_57_; uint8_t v___x_58_; 
v_k_x27_57_ = lean_array_fget_borrowed(v_keys_52_, v_i_53_);
v___x_58_ = lean_name_eq(v_k_54_, v_k_x27_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_add(v_i_53_, v___x_59_);
lean_dec(v_i_53_);
v_i_53_ = v___x_60_;
goto _start;
}
else
{
lean_dec(v_i_53_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_52_ = stack[0].m_obj;
lean_object* v_i_53_ = stack[1].m_obj;
lean_object* v_k_54_ = stack[2].m_obj;
uint8_t v_res_62_;
v_res_62_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_keys_52_, v_i_53_, v_k_54_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_63_, lean_object* v_i_64_, lean_object* v_k_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_keys_63_, v_i_64_, v_k_65_);
lean_dec(v_k_65_);
lean_dec_ref(v_keys_63_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(lean_object* v_x_68_, size_t v_x_69_, lean_object* v_x_70_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v_es_71_; lean_object* v___x_72_; size_t v___x_73_; size_t v___x_74_; lean_object* v_j_75_; lean_object* v___x_76_; 
v_es_71_ = lean_ctor_get(v_x_68_, 0);
v___x_72_ = lean_box(2);
v___x_73_ = ((size_t)31ULL);
v___x_74_ = lean_usize_land(v_x_69_, v___x_73_);
v_j_75_ = lean_usize_to_nat(v___x_74_);
v___x_76_ = lean_array_get_borrowed(v___x_72_, v_es_71_, v_j_75_);
lean_dec(v_j_75_);
switch(lean_obj_tag(v___x_76_))
{
case 0:
{
lean_object* v_key_77_; uint8_t v___x_78_; 
v_key_77_ = lean_ctor_get(v___x_76_, 0);
v___x_78_ = lean_name_eq(v_x_70_, v_key_77_);
return v___x_78_;
}
case 1:
{
lean_object* v_node_79_; size_t v___x_80_; size_t v___x_81_; 
v_node_79_ = lean_ctor_get(v___x_76_, 0);
v___x_80_ = ((size_t)5ULL);
v___x_81_ = lean_usize_shift_right(v_x_69_, v___x_80_);
v_x_68_ = v_node_79_;
v_x_69_ = v___x_81_;
goto _start;
}
default: 
{
uint8_t v___x_83_; 
v___x_83_ = 0;
return v___x_83_;
}
}
}
else
{
lean_object* v_ks_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_ks_84_ = lean_ctor_get(v_x_68_, 0);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_ks_84_, v___x_85_, v_x_70_);
return v___x_86_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_68_ = stack[0].m_obj;
size_t v_x_69_ = stack[1].m_num;
lean_object* v_x_70_ = stack[2].m_obj;
uint8_t v_res_87_;
v_res_87_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_68_, v_x_69_, v_x_70_);
stack->m_num = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
size_t v_x_128__boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_x_128__boxed_91_ = lean_unbox_usize(v_x_89_);
lean_dec(v_x_89_);
v_res_92_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_88_, v_x_128__boxed_91_, v_x_90_);
lean_dec(v_x_90_);
lean_dec_ref(v_x_88_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
uint64_t v___y_97_; 
if (lean_obj_tag(v_x_95_) == 0)
{
uint64_t v___x_100_; 
v___x_100_ = 1723ULL;
v___y_97_ = v___x_100_;
goto v___jp_96_;
}
else
{
uint64_t v_hash_101_; 
v_hash_101_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2);
v___y_97_ = v_hash_101_;
goto v___jp_96_;
}
v___jp_96_:
{
size_t v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_uint64_to_usize(v___y_97_);
v___x_99_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_94_, v___x_98_, v_x_95_);
return v___x_99_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_94_ = stack[0].m_obj;
lean_object* v_x_95_ = stack[1].m_obj;
uint8_t v_res_102_;
v_res_102_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_94_, v_x_95_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___boxed(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_103_, v_x_104_);
lean_dec(v_x_104_);
lean_dec_ref(v_x_103_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object* v_s_107_, lean_object* v_declName_108_){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_s_107_, v_declName_108_);
return v___x_109_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CasesTypes_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_107_ = stack[0].m_obj;
lean_object* v_declName_108_ = stack[1].m_obj;
uint8_t v_res_110_;
v_res_110_ = l_Lean_Meta_Grind_CasesTypes_contains(v_s_107_, v_declName_108_);
stack->m_num = v_res_110_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_contains___boxed(lean_object* v_s_111_, lean_object* v_declName_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_Lean_Meta_Grind_CasesTypes_contains(v_s_111_, v_declName_112_);
lean_dec(v_declName_112_);
lean_dec_ref(v_s_111_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(lean_object* v_00_u03b2_115_, lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
uint8_t v___x_118_; 
v___x_118_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_116_, v_x_117_);
return v___x_118_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_116_ = stack[1].m_obj;
lean_object* v_x_117_ = stack[2].m_obj;
uint8_t v_res_119_;
v_res_119_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(lean_box(0), v_x_116_, v_x_117_);
stack->m_num = v_res_119_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___boxed(lean_object* v_00_u03b2_120_, lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(v_00_u03b2_120_, v_x_121_, v_x_122_);
lean_dec(v_x_122_);
lean_dec_ref(v_x_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(lean_object* v_00_u03b2_125_, lean_object* v_x_126_, size_t v_x_127_, lean_object* v_x_128_){
_start:
{
uint8_t v___x_129_; 
v___x_129_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_126_, v_x_127_, v_x_128_);
return v___x_129_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_126_ = stack[1].m_obj;
size_t v_x_127_ = stack[2].m_num;
lean_object* v_x_128_ = stack[3].m_obj;
uint8_t v_res_130_;
v_res_130_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(lean_box(0), v_x_126_, v_x_127_, v_x_128_);
stack->m_num = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_131_, lean_object* v_x_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
size_t v_x_231__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_x_231__boxed_135_ = lean_unbox_usize(v_x_133_);
lean_dec(v_x_133_);
v_res_136_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(v_00_u03b2_131_, v_x_132_, v_x_231__boxed_135_, v_x_134_);
lean_dec(v_x_134_);
lean_dec_ref(v_x_132_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_138_, lean_object* v_keys_139_, lean_object* v_vals_140_, lean_object* v_heq_141_, lean_object* v_i_142_, lean_object* v_k_143_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_keys_139_, v_i_142_, v_k_143_);
return v___x_144_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_139_ = stack[1].m_obj;
lean_object* v_vals_140_ = stack[2].m_obj;
lean_object* v_i_142_ = stack[4].m_obj;
lean_object* v_k_143_ = stack[5].m_obj;
uint8_t v_res_145_;
v_res_145_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(lean_box(0), v_keys_139_, v_vals_140_, lean_box(0), v_i_142_, v_k_143_);
stack->m_num = v_res_145_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_146_, lean_object* v_keys_147_, lean_object* v_vals_148_, lean_object* v_heq_149_, lean_object* v_i_150_, lean_object* v_k_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(v_00_u03b2_146_, v_keys_147_, v_vals_148_, v_heq_149_, v_i_150_, v_k_151_);
lean_dec(v_k_151_);
lean_dec_ref(v_vals_148_);
lean_dec_ref(v_keys_147_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(lean_object* v_xs_154_, lean_object* v_v_155_, lean_object* v_i_156_){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_array_get_size(v_xs_154_);
v___x_158_ = lean_nat_dec_lt(v_i_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
lean_dec(v_i_156_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_array_fget_borrowed(v_xs_154_, v_i_156_);
v___x_161_ = lean_name_eq(v___x_160_, v_v_155_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_i_156_, v___x_162_);
lean_dec(v_i_156_);
v_i_156_ = v___x_163_;
goto _start;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_i_156_);
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_xs_166_, lean_object* v_v_167_, lean_object* v_i_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(v_xs_166_, v_v_167_, v_i_168_);
lean_dec(v_v_167_);
lean_dec_ref(v_xs_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(lean_object* v_xs_170_, lean_object* v_v_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(v_xs_170_, v_v_171_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_174_, lean_object* v_v_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(v_xs_174_, v_v_175_);
lean_dec(v_v_175_);
lean_dec_ref(v_xs_174_);
return v_res_176_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(lean_object* v_x_177_, size_t v_x_178_, lean_object* v_x_179_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v_es_180_; lean_object* v___x_181_; size_t v___x_182_; size_t v___x_183_; lean_object* v_j_184_; lean_object* v_entry_185_; 
v_es_180_ = lean_ctor_get(v_x_177_, 0);
v___x_181_ = lean_box(2);
v___x_182_ = ((size_t)31ULL);
v___x_183_ = lean_usize_land(v_x_178_, v___x_182_);
v_j_184_ = lean_usize_to_nat(v___x_183_);
v_entry_185_ = lean_array_get(v___x_181_, v_es_180_, v_j_184_);
switch(lean_obj_tag(v_entry_185_))
{
case 0:
{
lean_object* v_key_186_; uint8_t v___x_187_; 
v_key_186_ = lean_ctor_get(v_entry_185_, 0);
lean_inc(v_key_186_);
lean_dec_ref_known(v_entry_185_, 2);
v___x_187_ = lean_name_eq(v_x_179_, v_key_186_);
lean_dec(v_key_186_);
if (v___x_187_ == 0)
{
lean_dec(v_j_184_);
return v_x_177_;
}
else
{
lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_195_; 
lean_inc_ref(v_es_180_);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_x_177_, 0);
lean_dec(v_unused_196_);
v___x_189_ = v_x_177_;
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
else
{
lean_dec(v_x_177_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = lean_array_set(v_es_180_, v_j_184_, v___x_181_);
lean_dec(v_j_184_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
case 1:
{
lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_231_; 
lean_inc_ref(v_es_180_);
v_isSharedCheck_231_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v_x_177_, 0);
lean_dec(v_unused_232_);
v___x_198_ = v_x_177_;
v_isShared_199_ = v_isSharedCheck_231_;
goto v_resetjp_197_;
}
else
{
lean_dec(v_x_177_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_231_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v_node_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_230_; 
v_node_200_ = lean_ctor_get(v_entry_185_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v_entry_185_);
if (v_isSharedCheck_230_ == 0)
{
v___x_202_ = v_entry_185_;
v_isShared_203_ = v_isSharedCheck_230_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_node_200_);
lean_dec(v_entry_185_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_230_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
size_t v___x_204_; lean_object* v_entries_205_; size_t v___x_206_; lean_object* v_newNode_207_; lean_object* v___x_208_; 
v___x_204_ = ((size_t)5ULL);
v_entries_205_ = lean_array_set(v_es_180_, v_j_184_, v___x_181_);
v___x_206_ = lean_usize_shift_right(v_x_178_, v___x_204_);
v_newNode_207_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_node_200_, v___x_206_, v_x_179_);
lean_inc_ref(v_newNode_207_);
v___x_208_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_210_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v_newNode_207_);
v___x_210_ = v___x_202_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_newNode_207_);
v___x_210_ = v_reuseFailAlloc_215_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_array_set(v_entries_205_, v_j_184_, v___x_210_);
lean_dec(v_j_184_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_211_);
v___x_213_ = v___x_198_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v_val_216_; lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_newNode_207_);
lean_del_object(v___x_202_);
v_val_216_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v___x_208_, 1);
v_fst_217_ = lean_ctor_get(v_val_216_, 0);
v_snd_218_ = lean_ctor_get(v_val_216_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_val_216_);
if (v_isSharedCheck_229_ == 0)
{
v___x_220_ = v_val_216_;
v_isShared_221_ = v_isSharedCheck_229_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_snd_218_);
lean_inc(v_fst_217_);
lean_dec(v_val_216_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_229_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_fst_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_snd_218_);
v___x_223_ = v_reuseFailAlloc_228_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_array_set(v_entries_205_, v_j_184_, v___x_223_);
lean_dec(v_j_184_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_224_);
v___x_226_ = v___x_198_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_184_);
return v_x_177_;
}
}
}
else
{
lean_object* v_ks_233_; lean_object* v_vs_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_248_; 
v_ks_233_ = lean_ctor_get(v_x_177_, 0);
v_vs_234_ = lean_ctor_get(v_x_177_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_248_ == 0)
{
v___x_236_ = v_x_177_;
v_isShared_237_ = v_isSharedCheck_248_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_vs_234_);
lean_inc(v_ks_233_);
lean_dec(v_x_177_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_248_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; 
v___x_238_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(v_ks_233_, v_x_179_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_240_; 
if (v_isShared_237_ == 0)
{
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_ks_233_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_vs_234_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v_val_242_; lean_object* v_keys_x27_243_; lean_object* v_vals_x27_244_; lean_object* v___x_246_; 
v_val_242_ = lean_ctor_get(v___x_238_, 0);
lean_inc_n(v_val_242_, 2);
lean_dec_ref_known(v___x_238_, 1);
v_keys_x27_243_ = l_Array_eraseIdx___redArg(v_ks_233_, v_val_242_);
v_vals_x27_244_ = l_Array_eraseIdx___redArg(v_vs_234_, v_val_242_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v_vals_x27_244_);
lean_ctor_set(v___x_236_, 0, v_keys_x27_243_);
v___x_246_ = v___x_236_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_keys_x27_243_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_vals_x27_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_177_ = stack[0].m_obj;
size_t v_x_178_ = stack[1].m_num;
lean_object* v_x_179_ = stack[2].m_obj;
lean_object* v_res_249_;
v_res_249_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_177_, v_x_178_, v_x_179_);
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
size_t v_x_189__boxed_253_; lean_object* v_res_254_; 
v_x_189__boxed_253_ = lean_unbox_usize(v_x_251_);
lean_dec(v_x_251_);
v_res_254_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_250_, v_x_189__boxed_253_, v_x_252_);
lean_dec(v_x_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
uint64_t v___y_258_; 
if (lean_obj_tag(v_x_256_) == 0)
{
uint64_t v___x_261_; 
v___x_261_ = 1723ULL;
v___y_258_ = v___x_261_;
goto v___jp_257_;
}
else
{
uint64_t v_hash_262_; 
v_hash_262_ = lean_ctor_get_uint64(v_x_256_, sizeof(void*)*2);
v___y_258_ = v_hash_262_;
goto v___jp_257_;
}
v___jp_257_:
{
size_t v_h_259_; lean_object* v___x_260_; 
v_h_259_ = lean_uint64_to_usize(v___y_258_);
v___x_260_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_255_, v_h_259_, v_x_256_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg___boxed(lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_x_263_, v_x_264_);
lean_dec(v_x_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase(lean_object* v_s_266_, lean_object* v_declName_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_s_266_, v_declName_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase___boxed(lean_object* v_s_269_, lean_object* v_declName_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Meta_Grind_CasesTypes_erase(v_s_269_, v_declName_270_);
lean_dec(v_declName_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(lean_object* v_00_u03b2_272_, lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_x_273_, v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___boxed(lean_object* v_00_u03b2_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(v_00_u03b2_276_, v_x_277_, v_x_278_);
lean_dec(v_x_278_);
return v_res_279_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(lean_object* v_00_u03b2_280_, lean_object* v_x_281_, size_t v_x_282_, lean_object* v_x_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_281_, v_x_282_, v_x_283_);
return v___x_284_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_281_ = stack[1].m_obj;
size_t v_x_282_ = stack[2].m_num;
lean_object* v_x_283_ = stack[3].m_obj;
lean_object* v_res_285_;
v_res_285_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(lean_box(0), v_x_281_, v_x_282_, v_x_283_);
stack->m_obj
 = v_res_285_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_286_, lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
size_t v_x_432__boxed_290_; lean_object* v_res_291_; 
v_x_432__boxed_290_ = lean_unbox_usize(v_x_288_);
lean_dec(v_x_288_);
v_res_291_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(v_00_u03b2_286_, v_x_287_, v_x_432__boxed_290_, v_x_289_);
lean_dec(v_x_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_292_, lean_object* v_vals_293_, lean_object* v_i_294_, lean_object* v_k_295_){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_array_get_size(v_keys_292_);
v___x_297_ = lean_nat_dec_lt(v_i_294_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
lean_dec(v_i_294_);
v___x_298_ = lean_box(0);
return v___x_298_;
}
else
{
lean_object* v_k_x27_299_; uint8_t v___x_300_; 
v_k_x27_299_ = lean_array_fget_borrowed(v_keys_292_, v_i_294_);
v___x_300_ = lean_name_eq(v_k_295_, v_k_x27_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_i_294_, v___x_301_);
lean_dec(v_i_294_);
v_i_294_ = v___x_302_;
goto _start;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_array_fget_borrowed(v_vals_293_, v_i_294_);
lean_dec(v_i_294_);
lean_inc(v___x_304_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_306_, lean_object* v_vals_307_, lean_object* v_i_308_, lean_object* v_k_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_306_, v_vals_307_, v_i_308_, v_k_309_);
lean_dec(v_k_309_);
lean_dec_ref(v_vals_307_);
lean_dec_ref(v_keys_306_);
return v_res_310_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_311_, size_t v_x_312_, lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
lean_object* v_es_314_; lean_object* v___x_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v_j_318_; lean_object* v___x_319_; 
v_es_314_ = lean_ctor_get(v_x_311_, 0);
v___x_315_ = lean_box(2);
v___x_316_ = ((size_t)31ULL);
v___x_317_ = lean_usize_land(v_x_312_, v___x_316_);
v_j_318_ = lean_usize_to_nat(v___x_317_);
v___x_319_ = lean_array_get_borrowed(v___x_315_, v_es_314_, v_j_318_);
lean_dec(v_j_318_);
switch(lean_obj_tag(v___x_319_))
{
case 0:
{
lean_object* v_key_320_; lean_object* v_val_321_; uint8_t v___x_322_; 
v_key_320_ = lean_ctor_get(v___x_319_, 0);
v_val_321_ = lean_ctor_get(v___x_319_, 1);
v___x_322_ = lean_name_eq(v_x_313_, v_key_320_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_box(0);
return v___x_323_;
}
else
{
lean_object* v___x_324_; 
lean_inc(v_val_321_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_val_321_);
return v___x_324_;
}
}
case 1:
{
lean_object* v_node_325_; size_t v___x_326_; size_t v___x_327_; 
v_node_325_ = lean_ctor_get(v___x_319_, 0);
v___x_326_ = ((size_t)5ULL);
v___x_327_ = lean_usize_shift_right(v_x_312_, v___x_326_);
v_x_311_ = v_node_325_;
v_x_312_ = v___x_327_;
goto _start;
}
default: 
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
return v___x_329_;
}
}
}
else
{
lean_object* v_ks_330_; lean_object* v_vs_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_ks_330_ = lean_ctor_get(v_x_311_, 0);
v_vs_331_ = lean_ctor_get(v_x_311_, 1);
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_330_, v_vs_331_, v___x_332_, v_x_313_);
return v___x_333_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_311_ = stack[0].m_obj;
size_t v_x_312_ = stack[1].m_num;
lean_object* v_x_313_ = stack[2].m_obj;
lean_object* v_res_334_;
v_res_334_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_311_, v_x_312_, v_x_313_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
size_t v_x_147__boxed_338_; lean_object* v_res_339_; 
v_x_147__boxed_338_ = lean_unbox_usize(v_x_336_);
lean_dec(v_x_336_);
v_res_339_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_335_, v_x_147__boxed_338_, v_x_337_);
lean_dec(v_x_337_);
lean_dec_ref(v_x_335_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
uint64_t v___y_343_; 
if (lean_obj_tag(v_x_341_) == 0)
{
uint64_t v___x_346_; 
v___x_346_ = 1723ULL;
v___y_343_ = v___x_346_;
goto v___jp_342_;
}
else
{
uint64_t v_hash_347_; 
v_hash_347_ = lean_ctor_get_uint64(v_x_341_, sizeof(void*)*2);
v___y_343_ = v_hash_347_;
goto v___jp_342_;
}
v___jp_342_:
{
size_t v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_uint64_to_usize(v___y_343_);
v___x_345_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_340_, v___x_344_, v_x_341_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg___boxed(lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_x_348_, v_x_349_);
lean_dec(v_x_349_);
lean_dec_ref(v_x_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f(lean_object* v_s_351_, lean_object* v_declName_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_351_, v_declName_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f___boxed(lean_object* v_s_354_, lean_object* v_declName_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Meta_Grind_CasesTypes_find_x3f(v_s_354_, v_declName_355_);
lean_dec(v_declName_355_);
lean_dec_ref(v_s_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(lean_object* v_00_u03b2_357_, lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_x_358_, v_x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(v_00_u03b2_361_, v_x_362_, v_x_363_);
lean_dec(v_x_363_);
lean_dec_ref(v_x_362_);
return v_res_364_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_365_, lean_object* v_x_366_, size_t v_x_367_, lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_366_, v_x_367_, v_x_368_);
return v___x_369_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_366_ = stack[1].m_obj;
size_t v_x_367_ = stack[2].m_num;
lean_object* v_x_368_ = stack[3].m_obj;
lean_object* v_res_370_;
v_res_370_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(lean_box(0), v_x_366_, v_x_367_, v_x_368_);
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
size_t v_x_260__boxed_375_; lean_object* v_res_376_; 
v_x_260__boxed_375_ = lean_unbox_usize(v_x_373_);
lean_dec(v_x_373_);
v_res_376_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(v_00_u03b2_371_, v_x_372_, v_x_260__boxed_375_, v_x_374_);
lean_dec(v_x_374_);
lean_dec_ref(v_x_372_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_377_, lean_object* v_keys_378_, lean_object* v_vals_379_, lean_object* v_heq_380_, lean_object* v_i_381_, lean_object* v_k_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_378_, v_vals_379_, v_i_381_, v_k_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_384_, lean_object* v_keys_385_, lean_object* v_vals_386_, lean_object* v_heq_387_, lean_object* v_i_388_, lean_object* v_k_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_384_, v_keys_385_, v_vals_386_, v_heq_387_, v_i_388_, v_k_389_);
lean_dec(v_k_389_);
lean_dec_ref(v_vals_386_);
lean_dec_ref(v_keys_385_);
return v_res_390_;
}
}
uint8_t l_Lean_Meta_Grind_CasesTypes_isEagerSplit(lean_object* v_s_391_, lean_object* v_declName_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_391_, v_declName_392_);
if (lean_obj_tag(v___x_393_) == 0)
{
uint8_t v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_392_);
return v___x_394_;
}
else
{
lean_object* v_val_395_; uint8_t v___x_396_; 
v_val_395_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___x_393_, 1);
v___x_396_ = lean_unbox(v_val_395_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; 
lean_dec(v_val_395_);
v___x_397_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_392_);
return v___x_397_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = lean_unbox(v_val_395_);
lean_dec(v_val_395_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CasesTypes_isEagerSplit_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_391_ = stack[0].m_obj;
lean_object* v_declName_392_ = stack[1].m_obj;
uint8_t v_res_399_;
v_res_399_ = l_Lean_Meta_Grind_CasesTypes_isEagerSplit(v_s_391_, v_declName_392_);
stack->m_num = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isEagerSplit___boxed(lean_object* v_s_400_, lean_object* v_declName_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Lean_Meta_Grind_CasesTypes_isEagerSplit(v_s_400_, v_declName_401_);
lean_dec(v_declName_401_);
lean_dec_ref(v_s_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object* v_s_404_, lean_object* v_declName_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_404_, v_declName_405_);
if (lean_obj_tag(v___x_406_) == 0)
{
uint8_t v___x_407_; 
v___x_407_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_405_);
return v___x_407_;
}
else
{
uint8_t v___x_408_; 
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = 1;
return v___x_408_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CasesTypes_isSplit_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_404_ = stack[0].m_obj;
lean_object* v_declName_405_ = stack[1].m_obj;
uint8_t v_res_409_;
v_res_409_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_s_404_, v_declName_405_);
stack->m_num = v_res_409_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isSplit___boxed(lean_object* v_s_410_, lean_object* v_declName_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_s_410_, v_declName_411_);
lean_dec(v_declName_411_);
lean_dec_ref(v_s_410_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(lean_object* v_declName_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; lean_object* v_env_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = lean_st_ref_get(v___y_415_);
v_env_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc_ref(v_env_418_);
lean_dec(v___x_417_);
v___x_419_ = l_Lean_isInductiveCore_x3f(v_env_418_, v_declName_414_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT void l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_414_ = stack[0].m_obj;
lean_object* v___y_415_ = stack[1].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_414_, v___y_415_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg___boxed(lean_object* v_declName_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_422_, v___y_423_);
lean_dec(v___y_423_);
return v_res_425_;
}
}
lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(lean_object* v_declName_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_426_, v___y_428_);
return v___x_430_;
}
}
LEAN_EXPORT void l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_426_ = stack[0].m_obj;
lean_object* v___y_427_ = stack[1].m_obj;
lean_object* v___y_428_ = stack[2].m_obj;
lean_object* v_res_431_;
v_res_431_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(v_declName_426_, v___y_427_, v___y_428_);
stack->m_obj
 = v_res_431_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___boxed(lean_object* v_declName_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(v_declName_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_436_;
}
}
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object* v_declName_437_, uint8_t v_eager_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_464_; 
lean_inc(v_declName_437_);
v___x_442_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_437_, v_a_440_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_464_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_464_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_464_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
if (lean_obj_tag(v_a_443_) == 1)
{
lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_461_; 
v_val_452_ = lean_ctor_get(v_a_443_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_461_ == 0)
{
v___x_454_ = v_a_443_;
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_dec(v_a_443_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint8_t v_isRec_456_; 
v_isRec_456_ = lean_ctor_get_uint8(v_val_452_, sizeof(void*)*6);
lean_dec(v_val_452_);
if (v_isRec_456_ == 0)
{
lean_del_object(v___x_454_);
goto v___jp_447_;
}
else
{
if (v_eager_438_ == 0)
{
lean_del_object(v___x_454_);
goto v___jp_447_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_del_object(v___x_445_);
lean_dec(v_declName_437_);
v___x_457_ = lean_box(0);
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 0);
lean_ctor_set(v___x_454_, 0, v___x_457_);
v___x_459_ = v___x_454_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_del_object(v___x_445_);
lean_dec(v_a_443_);
lean_dec(v_declName_437_);
v___x_462_ = lean_box(0);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
v___jp_447_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_declName_437_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_448_);
v___x_450_ = v___x_445_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isCasesAttrCandidate_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_437_ = stack[0].m_obj;
uint8_t v_eager_438_ = stack[1].m_num;
lean_object* v_a_439_ = stack[2].m_obj;
lean_object* v_a_440_ = stack[3].m_obj;
lean_object* v_res_465_;
v_res_465_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_437_, v_eager_438_, v_a_439_, v_a_440_);
stack->m_obj
 = v_res_465_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f___boxed(lean_object* v_declName_466_, lean_object* v_eager_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
uint8_t v_eager_boxed_471_; lean_object* v_res_472_; 
v_eager_boxed_471_ = lean_unbox(v_eager_467_);
v_res_472_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_466_, v_eager_boxed_471_, v_a_468_, v_a_469_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
return v_res_472_;
}
}
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object* v_declName_473_, uint8_t v_eager_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_473_, v_eager_474_, v_a_475_, v_a_476_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_493_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_493_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_493_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_493_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
if (lean_obj_tag(v_a_479_) == 0)
{
uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_483_ = 0;
v___x_484_ = lean_box(v___x_483_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
else
{
uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
lean_dec_ref_known(v_a_479_, 1);
v___x_488_ = 1;
v___x_489_ = lean_box(v___x_488_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_489_);
v___x_491_ = v___x_481_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_a_494_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_478_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_478_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isCasesAttrCandidate_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_473_ = stack[0].m_obj;
uint8_t v_eager_474_ = stack[1].m_num;
lean_object* v_a_475_ = stack[2].m_obj;
lean_object* v_a_476_ = stack[3].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_473_, v_eager_474_, v_a_475_, v_a_476_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate___boxed(lean_object* v_declName_503_, lean_object* v_eager_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
uint8_t v_eager_boxed_508_; lean_object* v_res_509_; 
v_eager_boxed_508_ = lean_unbox(v_eager_504_);
v_res_509_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_503_, v_eager_boxed_508_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
return v_res_509_;
}
}
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object* v_declName_510_, uint8_t v_eager_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_510_, v_eager_511_, v_a_514_, v_a_515_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_528_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_528_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
if (lean_obj_tag(v_a_518_) == 1)
{
lean_object* v_val_522_; lean_object* v___x_523_; 
lean_del_object(v___x_520_);
v_val_522_ = lean_ctor_get(v_a_518_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v_a_518_, 1);
v___x_523_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_522_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_a_518_);
v___x_524_ = lean_box(0);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_524_);
v___x_526_ = v___x_520_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
v_a_529_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_517_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_517_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_510_ = stack[0].m_obj;
uint8_t v_eager_511_ = stack[1].m_num;
lean_object* v_a_512_ = stack[2].m_obj;
lean_object* v_a_513_ = stack[3].m_obj;
lean_object* v_a_514_ = stack[4].m_obj;
lean_object* v_a_515_ = stack[5].m_obj;
lean_object* v_res_537_;
v_res_537_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_510_, v_eager_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f___boxed(lean_object* v_declName_538_, lean_object* v_eager_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
uint8_t v_eager_boxed_545_; lean_object* v_res_546_; 
v_eager_boxed_545_ = lean_unbox(v_eager_539_);
v_res_546_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_538_, v_eager_boxed_545_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
return v_res_546_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_547_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_550_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_551_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
lean_ctor_set(v___x_553_, 2, v___x_552_);
lean_ctor_set(v___x_553_, 3, v___x_552_);
lean_ctor_set(v___x_553_, 4, v___x_551_);
lean_ctor_set(v___x_553_, 5, v___x_551_);
lean_ctor_set(v___x_553_, 6, v___x_551_);
lean_ctor_set(v___x_553_, 7, v___x_551_);
lean_ctor_set(v___x_553_, 8, v___x_551_);
lean_ctor_set(v___x_553_, 9, v___x_551_);
lean_ctor_set(v___x_553_, 10, v___x_551_);
lean_ctor_set(v___x_553_, 11, v___x_550_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(32u);
v___x_555_ = lean_mk_empty_array_with_capacity(v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_557_ = ((size_t)5ULL);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_unsigned_to_nat(32u);
v___x_560_ = lean_mk_empty_array_with_capacity(v___x_559_);
v___x_561_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3);
v___x_562_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
lean_ctor_set(v___x_562_, 2, v___x_558_);
lean_ctor_set(v___x_562_, 3, v___x_558_);
lean_ctor_set_usize(v___x_562_, 4, v___x_557_);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_563_ = lean_box(1);
v___x_564_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4);
v___x_565_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1);
v___x_566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_564_);
lean_ctor_set(v___x_566_, 2, v___x_563_);
return v___x_566_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(lean_object* v_msgData_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; lean_object* v_toCold_572_; lean_object* v_env_573_; lean_object* v_options_574_; uint8_t v___x_575_; lean_object* v_env_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_571_ = lean_st_ref_get(v___y_569_);
v_toCold_572_ = lean_ctor_get(v___y_568_, 0);
v_env_573_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_env_573_);
lean_dec(v___x_571_);
v_options_574_ = lean_ctor_get(v_toCold_572_, 2);
v___x_575_ = 0;
v_env_576_ = l_Lean_Environment_setRecordingDeps(v_env_573_, v___x_575_);
v___x_577_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2);
v___x_578_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_574_);
v___x_579_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_579_, 0, v_env_576_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
lean_ctor_set(v___x_579_, 2, v___x_578_);
lean_ctor_set(v___x_579_, 3, v_options_574_);
v___x_580_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_msgData_567_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_567_ = stack[0].m_obj;
lean_object* v___y_568_ = stack[1].m_obj;
lean_object* v___y_569_ = stack[2].m_obj;
lean_object* v_res_582_;
v_res_582_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msgData_567_, v___y_568_, v___y_569_);
stack->m_obj
 = v_res_582_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___boxed(lean_object* v_msgData_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msgData_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_587_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(lean_object* v_msg_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_ref_592_; lean_object* v___x_593_; lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_602_; 
v_ref_592_ = lean_ctor_get(v___y_589_, 2);
v___x_593_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msg_588_, v___y_589_, v___y_590_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_602_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
lean_inc(v_ref_592_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_ref_592_);
lean_ctor_set(v___x_598_, 1, v_a_594_);
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 1);
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_588_ = stack[0].m_obj;
lean_object* v___y_589_ = stack[1].m_obj;
lean_object* v___y_590_ = stack[2].m_obj;
lean_object* v_res_603_;
v_res_603_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v_msg_588_, v___y_589_, v___y_590_);
stack->m_obj
 = v_res_603_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg___boxed(lean_object* v_msg_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v_msg_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_608_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__1(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__0));
v___x_611_ = l_Lean_stringToMessageData(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__3(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__2));
v___x_614_ = l_Lean_stringToMessageData(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__5(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__4));
v___x_617_ = l_Lean_stringToMessageData(v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__7(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__6));
v___x_620_ = l_Lean_stringToMessageData(v___x_619_);
return v___x_620_;
}
}
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object* v_declName_621_, uint8_t v_eager_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v___x_626_; 
lean_inc(v_declName_621_);
v___x_626_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_621_, v_eager_622_, v_a_623_, v_a_624_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_649_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_649_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_649_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_649_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
uint8_t v___x_631_; 
v___x_631_ = lean_unbox(v_a_627_);
if (v___x_631_ == 0)
{
lean_del_object(v___x_629_);
if (v_eager_622_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec(v_a_627_);
v___x_632_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__1, &l_Lean_Meta_Grind_validateCasesAttr___closed__1_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__1);
v___x_633_ = l_Lean_MessageData_ofConstName(v_declName_621_, v_eager_622_);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__3, &l_Lean_Meta_Grind_validateCasesAttr___closed__3_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__3);
v___x_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_636_, v_a_623_, v_a_624_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_638_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__5, &l_Lean_Meta_Grind_validateCasesAttr___closed__5_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__5);
v___x_639_ = lean_unbox(v_a_627_);
lean_dec(v_a_627_);
v___x_640_ = l_Lean_MessageData_ofConstName(v_declName_621_, v___x_639_);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_638_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__7, &l_Lean_Meta_Grind_validateCasesAttr___closed__7_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__7);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_643_, v_a_623_, v_a_624_);
return v___x_644_;
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_647_; 
lean_dec(v_a_627_);
lean_dec(v_declName_621_);
v___x_645_ = lean_box(0);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_645_);
v___x_647_ = v___x_629_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v_declName_621_);
v_a_650_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_626_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_626_);
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
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_validateCasesAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_621_ = stack[0].m_obj;
uint8_t v_eager_622_ = stack[1].m_num;
lean_object* v_a_623_ = stack[2].m_obj;
lean_object* v_a_624_ = stack[3].m_obj;
lean_object* v_res_658_;
v_res_658_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_621_, v_eager_622_, v_a_623_, v_a_624_);
stack->m_obj
 = v_res_658_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr___boxed(lean_object* v_declName_659_, lean_object* v_eager_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
uint8_t v_eager_boxed_664_; lean_object* v_res_665_; 
v_eager_boxed_664_ = lean_unbox(v_eager_660_);
v_res_665_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_659_, v_eager_boxed_664_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
return v_res_665_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(lean_object* v_00_u03b1_666_, lean_object* v_msg_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v_msg_667_, v___y_668_, v___y_669_);
return v___x_671_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_667_ = stack[1].m_obj;
lean_object* v___y_668_ = stack[2].m_obj;
lean_object* v___y_669_ = stack[3].m_obj;
lean_object* v_res_672_;
v_res_672_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(lean_box(0), v_msg_667_, v___y_668_, v___y_669_);
stack->m_obj
 = v_res_672_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_673_, lean_object* v_msg_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(v_00_u03b1_673_, v_msg_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v_res_678_;
}
}
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object* v_s_679_, lean_object* v_declName_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_s_679_, v_declName_680_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
lean_dec_ref(v_s_679_);
v___x_685_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_680_, v_a_681_, v_a_682_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_s_679_, v_declName_680_);
lean_dec(v_declName_680_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CasesTypes_eraseDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_679_ = stack[0].m_obj;
lean_object* v_declName_680_ = stack[1].m_obj;
lean_object* v_a_681_ = stack[2].m_obj;
lean_object* v_a_682_ = stack[3].m_obj;
lean_object* v_res_688_;
v_res_688_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_s_679_, v_declName_680_, v_a_681_, v_a_682_);
stack->m_obj
 = v_res_688_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl___boxed(lean_object* v_s_689_, lean_object* v_declName_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_s_689_, v_declName_690_, v_a_691_, v_a_692_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
return v_res_694_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object* v_declName_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
uint8_t v___x_705_; 
v___x_705_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_701_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec(v_declName_701_);
v___x_706_ = lean_box(0);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_708_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1);
v___x_709_ = 0;
v___x_710_ = l_Lean_MessageData_ofConstName(v_declName_701_, v___x_709_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_708_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_713_, v_a_702_, v_a_703_);
return v___x_714_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_ensureNotBuiltinCases_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_701_ = stack[0].m_obj;
lean_object* v_a_702_ = stack[1].m_obj;
lean_object* v_a_703_ = stack[2].m_obj;
lean_object* v_res_715_;
v_res_715_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_701_, v_a_702_, v_a_703_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___boxed(lean_object* v_declName_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
return v_res_720_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(lean_object* v_e_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
if (lean_obj_tag(v_e_721_) == 1)
{
lean_object* v_fvarId_727_; lean_object* v___x_728_; 
v_fvarId_727_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_fvarId_727_);
lean_dec_ref_known(v_e_721_, 1);
v___x_728_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_727_, v_a_722_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_745_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_745_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_745_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_745_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_lctx_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_lctx_733_ = lean_ctor_get(v_a_722_, 2);
v___x_734_ = l_Lean_LocalDecl_index(v_a_729_);
lean_inc_ref(v_lctx_733_);
v___x_735_ = lean_local_ctx_num_indices(v_lctx_733_);
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_sub(v___x_735_, v___x_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_nat_dec_eq(v___x_734_, v___x_737_);
lean_dec(v___x_737_);
lean_dec(v___x_734_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_del_object(v___x_731_);
v___x_739_ = l_Lean_LocalDecl_type(v_a_729_);
lean_dec(v_a_729_);
v___x_740_ = l_Lean_Meta_isProp(v___x_739_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_743_; 
lean_dec(v_a_729_);
v___x_741_ = lean_box(v___x_738_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_741_);
v___x_743_ = v___x_731_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
v_a_746_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_728_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_728_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec_ref(v_e_721_);
v___x_754_ = 0;
v___x_755_ = lean_box(v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_721_ = stack[0].m_obj;
lean_object* v_a_722_ = stack[1].m_obj;
lean_object* v_a_723_ = stack[2].m_obj;
lean_object* v_a_724_ = stack[3].m_obj;
lean_object* v_a_725_ = stack[4].m_obj;
lean_object* v_res_757_;
v_res_757_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(v_e_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
stack->m_obj
 = v_res_757_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar___boxed(lean_object* v_e_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(v_e_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
return v_res_764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(lean_object* v_mvarId_773_, lean_object* v_e_774_, lean_object* v_type_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
v___x_782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4);
v___x_783_ = l_Lean_MessageData_ofExpr(v_e_774_);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Lean_indentExpr(v_type_775_);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
v___x_788_ = l_Lean_Meta_throwTacticEx___redArg(v___x_781_, v_mvarId_773_, v___x_787_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
return v___x_788_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_773_ = stack[0].m_obj;
lean_object* v_e_774_ = stack[1].m_obj;
lean_object* v_type_775_ = stack[2].m_obj;
lean_object* v_a_776_ = stack[3].m_obj;
lean_object* v_a_777_ = stack[4].m_obj;
lean_object* v_a_778_ = stack[5].m_obj;
lean_object* v_a_779_ = stack[6].m_obj;
lean_object* v_res_789_;
v_res_789_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_773_, v_e_774_, v_type_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
stack->m_obj
 = v_res_789_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___boxed(lean_object* v_mvarId_790_, lean_object* v_e_791_, lean_object* v_type_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_790_, v_e_791_, v_type_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
return v_res_798_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(lean_object* v_mvarId_799_, lean_object* v_e_800_, lean_object* v_00_u03b1_801_, lean_object* v_type_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_799_, v_e_800_, v_type_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
return v___x_808_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_799_ = stack[0].m_obj;
lean_object* v_e_800_ = stack[1].m_obj;
lean_object* v_type_802_ = stack[3].m_obj;
lean_object* v_a_803_ = stack[4].m_obj;
lean_object* v_a_804_ = stack[5].m_obj;
lean_object* v_a_805_ = stack[6].m_obj;
lean_object* v_a_806_ = stack[7].m_obj;
lean_object* v_res_809_;
v_res_809_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(v_mvarId_799_, v_e_800_, lean_box(0), v_type_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
stack->m_obj
 = v_res_809_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___boxed(lean_object* v_mvarId_810_, lean_object* v_e_811_, lean_object* v_00_u03b1_812_, lean_object* v_type_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(v_mvarId_810_, v_e_811_, v_00_u03b1_812_, v_type_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_819_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(lean_object* v_mvarId_820_, lean_object* v_x_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_820_, v_x_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_827_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_827_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_820_ = stack[0].m_obj;
lean_object* v_x_821_ = stack[1].m_obj;
lean_object* v___y_822_ = stack[2].m_obj;
lean_object* v___y_823_ = stack[3].m_obj;
lean_object* v___y_824_ = stack[4].m_obj;
lean_object* v___y_825_ = stack[5].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_820_, v_x_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg___boxed(lean_object* v_mvarId_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_845_, v_x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_852_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(lean_object* v_00_u03b1_853_, lean_object* v_mvarId_854_, lean_object* v_x_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_854_, v_x_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_861_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_854_ = stack[1].m_obj;
lean_object* v_x_855_ = stack[2].m_obj;
lean_object* v___y_856_ = stack[3].m_obj;
lean_object* v___y_857_ = stack[4].m_obj;
lean_object* v___y_858_ = stack[5].m_obj;
lean_object* v___y_859_ = stack[6].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(lean_box(0), v_mvarId_854_, v_x_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___boxed(lean_object* v_00_u03b1_863_, lean_object* v_mvarId_864_, lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(v_00_u03b1_863_, v_mvarId_864_, v_x_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_871_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(lean_object* v_as_872_, size_t v_i_873_, size_t v_stop_874_, lean_object* v_b_875_){
_start:
{
uint8_t v___x_876_; 
v___x_876_ = lean_usize_dec_eq(v_i_873_, v_stop_874_);
if (v___x_876_ == 0)
{
uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; size_t v___x_880_; size_t v___x_881_; 
v___x_877_ = 1;
v___x_878_ = lean_array_uget_borrowed(v_as_872_, v_i_873_);
lean_inc(v___x_878_);
v___x_879_ = l_Lean_LocalContext_setKind(v_b_875_, v___x_878_, v___x_877_);
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_i_873_, v___x_880_);
v_i_873_ = v___x_881_;
v_b_875_ = v___x_879_;
goto _start;
}
else
{
return v_b_875_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_872_ = stack[0].m_obj;
size_t v_i_873_ = stack[1].m_num;
size_t v_stop_874_ = stack[2].m_num;
lean_object* v_b_875_ = stack[3].m_obj;
lean_object* v_res_883_;
v_res_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_as_872_, v_i_873_, v_stop_874_, v_b_875_);
stack->m_obj
 = v_res_883_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4___boxed(lean_object* v_as_884_, lean_object* v_i_885_, lean_object* v_stop_886_, lean_object* v_b_887_){
_start:
{
size_t v_i_boxed_888_; size_t v_stop_boxed_889_; lean_object* v_res_890_; 
v_i_boxed_888_ = lean_unbox_usize(v_i_885_);
lean_dec(v_i_885_);
v_stop_boxed_889_ = lean_unbox_usize(v_stop_886_);
lean_dec(v_stop_886_);
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_as_884_, v_i_boxed_888_, v_stop_boxed_889_, v_b_887_);
lean_dec_ref(v_as_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
lean_object* v_ks_895_; lean_object* v_vs_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_920_; 
v_ks_895_ = lean_ctor_get(v_x_891_, 0);
v_vs_896_ = lean_ctor_get(v_x_891_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_x_891_);
if (v_isSharedCheck_920_ == 0)
{
v___x_898_ = v_x_891_;
v_isShared_899_ = v_isSharedCheck_920_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_vs_896_);
lean_inc(v_ks_895_);
lean_dec(v_x_891_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_920_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_array_get_size(v_ks_895_);
v___x_901_ = lean_nat_dec_lt(v_x_892_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
lean_dec(v_x_892_);
v___x_902_ = lean_array_push(v_ks_895_, v_x_893_);
v___x_903_ = lean_array_push(v_vs_896_, v_x_894_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_903_);
lean_ctor_set(v___x_898_, 0, v___x_902_);
v___x_905_ = v___x_898_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
else
{
lean_object* v_k_x27_907_; uint8_t v___x_908_; 
v_k_x27_907_ = lean_array_fget_borrowed(v_ks_895_, v_x_892_);
v___x_908_ = l_Lean_instBEqMVarId_beq(v_x_893_, v_k_x27_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_910_; 
if (v_isShared_899_ == 0)
{
v___x_910_ = v___x_898_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_ks_895_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_vs_896_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v_x_892_, v___x_911_);
lean_dec(v_x_892_);
v_x_891_ = v___x_910_;
v_x_892_ = v___x_912_;
goto _start;
}
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_915_ = lean_array_fset(v_ks_895_, v_x_892_, v_x_893_);
v___x_916_ = lean_array_fset(v_vs_896_, v_x_892_, v_x_894_);
lean_dec(v_x_892_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_916_);
lean_ctor_set(v___x_898_, 0, v___x_915_);
v___x_918_ = v___x_898_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(lean_object* v_n_921_, lean_object* v_k_922_, lean_object* v_v_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(v_n_921_, v___x_924_, v_k_922_, v_v_923_);
return v___x_925_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_926_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(lean_object* v_x_927_, size_t v_x_928_, size_t v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
if (lean_obj_tag(v_x_927_) == 0)
{
lean_object* v_es_932_; size_t v___x_933_; size_t v___x_934_; lean_object* v_j_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_es_932_ = lean_ctor_get(v_x_927_, 0);
v___x_933_ = ((size_t)31ULL);
v___x_934_ = lean_usize_land(v_x_928_, v___x_933_);
v_j_935_ = lean_usize_to_nat(v___x_934_);
v___x_936_ = lean_array_get_size(v_es_932_);
v___x_937_ = lean_nat_dec_lt(v_j_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_dec(v_j_935_);
lean_dec(v_x_931_);
lean_dec(v_x_930_);
return v_x_927_;
}
else
{
lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_976_; 
lean_inc_ref(v_es_932_);
v_isSharedCheck_976_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_x_927_, 0);
lean_dec(v_unused_977_);
v___x_939_ = v_x_927_;
v_isShared_940_ = v_isSharedCheck_976_;
goto v_resetjp_938_;
}
else
{
lean_dec(v_x_927_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_976_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_v_941_; lean_object* v___x_942_; lean_object* v_xs_x27_943_; lean_object* v___y_945_; 
v_v_941_ = lean_array_fget(v_es_932_, v_j_935_);
v___x_942_ = lean_box(0);
v_xs_x27_943_ = lean_array_fset(v_es_932_, v_j_935_, v___x_942_);
switch(lean_obj_tag(v_v_941_))
{
case 0:
{
lean_object* v_key_950_; lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_961_; 
v_key_950_ = lean_ctor_get(v_v_941_, 0);
v_val_951_ = lean_ctor_get(v_v_941_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_v_941_);
if (v_isSharedCheck_961_ == 0)
{
v___x_953_ = v_v_941_;
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_inc(v_key_950_);
lean_dec(v_v_941_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_instBEqMVarId_beq(v_x_930_, v_key_950_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_del_object(v___x_953_);
v___x_956_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_950_, v_val_951_, v_x_930_, v_x_931_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
v___y_945_ = v___x_957_;
goto v___jp_944_;
}
else
{
lean_object* v___x_959_; 
lean_dec(v_val_951_);
lean_dec(v_key_950_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_x_931_);
lean_ctor_set(v___x_953_, 0, v_x_930_);
v___x_959_ = v___x_953_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_x_930_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_x_931_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
v___y_945_ = v___x_959_;
goto v___jp_944_;
}
}
}
}
case 1:
{
lean_object* v_node_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_974_; 
v_node_962_ = lean_ctor_get(v_v_941_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v_v_941_);
if (v_isSharedCheck_974_ == 0)
{
v___x_964_ = v_v_941_;
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_node_962_);
lean_dec(v_v_941_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
size_t v___x_966_; size_t v___x_967_; size_t v___x_968_; size_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_966_ = ((size_t)5ULL);
v___x_967_ = lean_usize_shift_right(v_x_928_, v___x_966_);
v___x_968_ = ((size_t)1ULL);
v___x_969_ = lean_usize_add(v_x_929_, v___x_968_);
v___x_970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_node_962_, v___x_967_, v___x_969_, v_x_930_, v_x_931_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_970_);
v___x_972_ = v___x_964_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
v___y_945_ = v___x_972_;
goto v___jp_944_;
}
}
}
default: 
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_x_930_);
lean_ctor_set(v___x_975_, 1, v_x_931_);
v___y_945_ = v___x_975_;
goto v___jp_944_;
}
}
v___jp_944_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_946_ = lean_array_fset(v_xs_x27_943_, v_j_935_, v___y_945_);
lean_dec(v_j_935_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_946_);
v___x_948_ = v___x_939_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
else
{
lean_object* v_ks_978_; lean_object* v_vs_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_997_; 
v_ks_978_ = lean_ctor_get(v_x_927_, 0);
v_vs_979_ = lean_ctor_get(v_x_927_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_997_ == 0)
{
v___x_981_ = v_x_927_;
v_isShared_982_ = v_isSharedCheck_997_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_vs_979_);
lean_inc(v_ks_978_);
lean_dec(v_x_927_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_997_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_ks_978_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_vs_979_);
v___x_984_ = v_reuseFailAlloc_996_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v_newNode_985_; size_t v___x_986_; uint8_t v___x_987_; 
v_newNode_985_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(v___x_984_, v_x_930_, v_x_931_);
v___x_986_ = ((size_t)7ULL);
v___x_987_ = lean_usize_dec_le(v___x_986_, v_x_929_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_988_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_985_);
v___x_989_ = lean_unsigned_to_nat(4u);
v___x_990_ = lean_nat_dec_lt(v___x_988_, v___x_989_);
lean_dec(v___x_988_);
if (v___x_990_ == 0)
{
lean_object* v_ks_991_; lean_object* v_vs_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_ks_991_ = lean_ctor_get(v_newNode_985_, 0);
lean_inc_ref(v_ks_991_);
v_vs_992_ = lean_ctor_get(v_newNode_985_, 1);
lean_inc_ref(v_vs_992_);
lean_dec_ref(v_newNode_985_);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_x_929_, v_ks_991_, v_vs_992_, v___x_993_, v___x_994_);
lean_dec_ref(v_vs_992_);
lean_dec_ref(v_ks_991_);
return v___x_995_;
}
else
{
return v_newNode_985_;
}
}
else
{
return v_newNode_985_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_927_ = stack[0].m_obj;
size_t v_x_928_ = stack[1].m_num;
size_t v_x_929_ = stack[2].m_num;
lean_object* v_x_930_ = stack[3].m_obj;
lean_object* v_x_931_ = stack[4].m_obj;
lean_object* v_res_998_;
v_res_998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_927_, v_x_928_, v_x_929_, v_x_930_, v_x_931_);
stack->m_obj
 = v_res_998_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(size_t v_depth_999_, lean_object* v_keys_1000_, lean_object* v_vals_1001_, lean_object* v_i_1002_, lean_object* v_entries_1003_){
_start:
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_array_get_size(v_keys_1000_);
v___x_1005_ = lean_nat_dec_lt(v_i_1002_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_dec(v_i_1002_);
return v_entries_1003_;
}
else
{
lean_object* v_k_1006_; lean_object* v_v_1007_; uint64_t v___x_1008_; size_t v_h_1009_; size_t v___x_1010_; lean_object* v___x_1011_; size_t v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; size_t v_h_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_k_1006_ = lean_array_fget_borrowed(v_keys_1000_, v_i_1002_);
v_v_1007_ = lean_array_fget_borrowed(v_vals_1001_, v_i_1002_);
v___x_1008_ = l_Lean_instHashableMVarId_hash(v_k_1006_);
v_h_1009_ = lean_uint64_to_usize(v___x_1008_);
v___x_1010_ = ((size_t)5ULL);
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = ((size_t)1ULL);
v___x_1013_ = lean_usize_sub(v_depth_999_, v___x_1012_);
v___x_1014_ = lean_usize_mul(v___x_1010_, v___x_1013_);
v_h_1015_ = lean_usize_shift_right(v_h_1009_, v___x_1014_);
v___x_1016_ = lean_nat_add(v_i_1002_, v___x_1011_);
lean_dec(v_i_1002_);
lean_inc(v_v_1007_);
lean_inc(v_k_1006_);
v___x_1017_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_entries_1003_, v_h_1015_, v_depth_999_, v_k_1006_, v_v_1007_);
v_i_1002_ = v___x_1016_;
v_entries_1003_ = v___x_1017_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_999_ = stack[0].m_num;
lean_object* v_keys_1000_ = stack[1].m_obj;
lean_object* v_vals_1001_ = stack[2].m_obj;
lean_object* v_i_1002_ = stack[3].m_obj;
lean_object* v_entries_1003_ = stack[4].m_obj;
lean_object* v_res_1019_;
v_res_1019_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_999_, v_keys_1000_, v_vals_1001_, v_i_1002_, v_entries_1003_);
stack->m_obj
 = v_res_1019_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg___boxed(lean_object* v_depth_1020_, lean_object* v_keys_1021_, lean_object* v_vals_1022_, lean_object* v_i_1023_, lean_object* v_entries_1024_){
_start:
{
size_t v_depth_boxed_1025_; lean_object* v_res_1026_; 
v_depth_boxed_1025_ = lean_unbox_usize(v_depth_1020_);
lean_dec(v_depth_1020_);
v_res_1026_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_boxed_1025_, v_keys_1021_, v_vals_1022_, v_i_1023_, v_entries_1024_);
lean_dec_ref(v_vals_1022_);
lean_dec_ref(v_keys_1021_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
size_t v_x_11976__boxed_1032_; size_t v_x_11977__boxed_1033_; lean_object* v_res_1034_; 
v_x_11976__boxed_1032_ = lean_unbox_usize(v_x_1028_);
lean_dec(v_x_1028_);
v_x_11977__boxed_1033_ = lean_unbox_usize(v_x_1029_);
lean_dec(v_x_1029_);
v_res_1034_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_1027_, v_x_11976__boxed_1032_, v_x_11977__boxed_1033_, v_x_1030_, v_x_1031_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
uint64_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1038_ = l_Lean_instHashableMVarId_hash(v_x_1036_);
v___x_1039_ = lean_uint64_to_usize(v___x_1038_);
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_1035_, v___x_1039_, v___x_1040_, v_x_1036_, v_x_1037_);
return v___x_1041_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(lean_object* v_mvarId_1042_, lean_object* v_val_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; lean_object* v_mctx_1047_; lean_object* v_cache_1048_; lean_object* v_zetaDeltaFVarIds_1049_; lean_object* v_postponed_1050_; lean_object* v_diag_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1081_; 
v___x_1046_ = lean_st_ref_take(v___y_1044_);
v_mctx_1047_ = lean_ctor_get(v___x_1046_, 0);
v_cache_1048_ = lean_ctor_get(v___x_1046_, 1);
v_zetaDeltaFVarIds_1049_ = lean_ctor_get(v___x_1046_, 2);
v_postponed_1050_ = lean_ctor_get(v___x_1046_, 3);
v_diag_1051_ = lean_ctor_get(v___x_1046_, 4);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1053_ = v___x_1046_;
v_isShared_1054_ = v_isSharedCheck_1081_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_diag_1051_);
lean_inc(v_postponed_1050_);
lean_inc(v_zetaDeltaFVarIds_1049_);
lean_inc(v_cache_1048_);
lean_inc(v_mctx_1047_);
lean_dec(v___x_1046_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1081_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_depth_1055_; lean_object* v_levelAssignDepth_1056_; lean_object* v_lmvarCounter_1057_; lean_object* v_mvarCounter_1058_; lean_object* v_lDecls_1059_; lean_object* v_decls_1060_; lean_object* v_userNames_1061_; lean_object* v_lAssignment_1062_; lean_object* v_eAssignment_1063_; lean_object* v_dAssignment_1064_; lean_object* v_instanceTypedMVars_1065_; lean_object* v_synthNormMemo_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1080_; 
v_depth_1055_ = lean_ctor_get(v_mctx_1047_, 0);
v_levelAssignDepth_1056_ = lean_ctor_get(v_mctx_1047_, 1);
v_lmvarCounter_1057_ = lean_ctor_get(v_mctx_1047_, 2);
v_mvarCounter_1058_ = lean_ctor_get(v_mctx_1047_, 3);
v_lDecls_1059_ = lean_ctor_get(v_mctx_1047_, 4);
v_decls_1060_ = lean_ctor_get(v_mctx_1047_, 5);
v_userNames_1061_ = lean_ctor_get(v_mctx_1047_, 6);
v_lAssignment_1062_ = lean_ctor_get(v_mctx_1047_, 7);
v_eAssignment_1063_ = lean_ctor_get(v_mctx_1047_, 8);
v_dAssignment_1064_ = lean_ctor_get(v_mctx_1047_, 9);
v_instanceTypedMVars_1065_ = lean_ctor_get(v_mctx_1047_, 10);
v_synthNormMemo_1066_ = lean_ctor_get(v_mctx_1047_, 11);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_mctx_1047_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1068_ = v_mctx_1047_;
v_isShared_1069_ = v_isSharedCheck_1080_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_synthNormMemo_1066_);
lean_inc(v_instanceTypedMVars_1065_);
lean_inc(v_dAssignment_1064_);
lean_inc(v_eAssignment_1063_);
lean_inc(v_lAssignment_1062_);
lean_inc(v_userNames_1061_);
lean_inc(v_decls_1060_);
lean_inc(v_lDecls_1059_);
lean_inc(v_mvarCounter_1058_);
lean_inc(v_lmvarCounter_1057_);
lean_inc(v_levelAssignDepth_1056_);
lean_inc(v_depth_1055_);
lean_dec(v_mctx_1047_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1080_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(v_eAssignment_1063_, v_mvarId_1042_, v_val_1043_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 8, v___x_1071_);
v___x_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_depth_1055_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_levelAssignDepth_1056_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_lmvarCounter_1057_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_mvarCounter_1058_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_lDecls_1059_);
lean_ctor_set(v_reuseFailAlloc_1079_, 5, v_decls_1060_);
lean_ctor_set(v_reuseFailAlloc_1079_, 6, v_userNames_1061_);
lean_ctor_set(v_reuseFailAlloc_1079_, 7, v_lAssignment_1062_);
lean_ctor_set(v_reuseFailAlloc_1079_, 8, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1079_, 9, v_dAssignment_1064_);
lean_ctor_set(v_reuseFailAlloc_1079_, 10, v_instanceTypedMVars_1065_);
lean_ctor_set(v_reuseFailAlloc_1079_, 11, v_synthNormMemo_1066_);
v___x_1073_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1073_);
v___x_1075_ = v___x_1053_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_cache_1048_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_zetaDeltaFVarIds_1049_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_postponed_1050_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v_diag_1051_);
v___x_1075_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_st_ref_put(v___y_1044_, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1070_);
return v___x_1077_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1042_ = stack[0].m_obj;
lean_object* v_val_1043_ = stack[1].m_obj;
lean_object* v___y_1044_ = stack[2].m_obj;
lean_object* v_res_1082_;
v_res_1082_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1042_, v_val_1043_, v___y_1044_);
stack->m_obj
 = v_res_1082_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg___boxed(lean_object* v_mvarId_1083_, lean_object* v_val_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1083_, v_val_1084_, v___y_1085_);
lean_dec(v___y_1085_);
return v_res_1087_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1));
v___x_1092_ = l_Lean_MessageData_ofFormat(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2);
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(lean_object* v_upperBound_1095_, lean_object* v___y_1096_, lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v_a_1099_, lean_object* v_mvarId_1100_, lean_object* v_a_1101_, lean_object* v_b_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
uint8_t v___x_1108_; 
v___x_1108_ = lean_nat_dec_lt(v_a_1101_, v_upperBound_1095_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; 
lean_dec(v_a_1101_);
lean_dec(v_mvarId_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v___y_1096_);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_b_1102_);
return v___x_1109_;
}
else
{
lean_object* v_snd_1110_; lean_object* v_snd_1111_; lean_object* v_fst_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1194_; 
v_snd_1110_ = lean_ctor_get(v_b_1102_, 1);
lean_inc(v_snd_1110_);
v_snd_1111_ = lean_ctor_get(v_snd_1110_, 1);
lean_inc(v_snd_1111_);
v_fst_1112_ = lean_ctor_get(v_b_1102_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_b_1102_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v_b_1102_, 1);
lean_dec(v_unused_1195_);
v___x_1114_ = v_b_1102_;
v_isShared_1115_ = v_isSharedCheck_1194_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_fst_1112_);
lean_dec(v_b_1102_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1194_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_fst_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1192_; 
v_fst_1116_ = lean_ctor_get(v_snd_1110_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_snd_1110_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v_snd_1110_, 1);
lean_dec(v_unused_1193_);
v___x_1118_ = v_snd_1110_;
v_isShared_1119_ = v_isSharedCheck_1192_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_fst_1116_);
lean_dec(v_snd_1110_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1192_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v_fst_1120_; lean_object* v_snd_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1191_; 
v_fst_1120_ = lean_ctor_get(v_snd_1111_, 0);
v_snd_1121_ = lean_ctor_get(v_snd_1111_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_snd_1111_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1123_ = v_snd_1111_;
v_isShared_1124_ = v_isSharedCheck_1191_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_snd_1121_);
lean_inc(v_fst_1120_);
lean_dec(v_snd_1111_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1191_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_a_1128_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
lean_inc(v___y_1106_);
lean_inc_ref(v___y_1105_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v_fst_1116_);
v___x_1132_ = lean_whnf(v_fst_1116_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
if (lean_obj_tag(v_a_1133_) == 7)
{
lean_object* v_binderType_1134_; lean_object* v_body_1135_; lean_object* v___y_1137_; uint8_t v___x_1162_; 
lean_dec(v_fst_1116_);
v_binderType_1134_ = lean_ctor_get(v_a_1133_, 1);
lean_inc_ref(v_binderType_1134_);
v_body_1135_ = lean_ctor_get(v_a_1133_, 2);
lean_inc_ref(v_body_1135_);
lean_dec_ref_known(v_a_1133_, 3);
v___x_1162_ = lean_nat_dec_lt(v___x_1126_, v___x_1098_);
if (v___x_1162_ == 0)
{
lean_inc(v_a_1099_);
v___y_1137_ = v_a_1099_;
goto v___jp_1136_;
}
else
{
lean_object* v___x_1163_; 
lean_inc(v_snd_1121_);
lean_inc(v_a_1099_);
v___x_1163_ = l_Lean_Name_num___override(v_a_1099_, v_snd_1121_);
v___y_1137_ = v___x_1163_;
goto v___jp_1136_;
}
v___jp_1136_:
{
uint8_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = 2;
lean_inc_ref(v___x_1097_);
lean_inc_ref(v___y_1096_);
v___x_1139_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_1096_, v___x_1097_, v_binderType_1134_, v___x_1138_, v___y_1137_, v___x_1125_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc_n(v_a_1140_, 2);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = l_Lean_Expr_app___override(v_fst_1112_, v_a_1140_);
v___x_1142_ = l_Lean_Expr_mvarId_x21(v_a_1140_);
lean_dec(v_a_1140_);
v___x_1143_ = lean_array_push(v_fst_1120_, v___x_1142_);
v___x_1144_ = lean_nat_add(v_snd_1121_, v___x_1126_);
lean_dec(v_snd_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v___x_1144_);
lean_ctor_set(v___x_1123_, 0, v___x_1143_);
v___x_1146_ = v___x_1123_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v___x_1146_);
lean_ctor_set(v___x_1118_, 0, v_body_1135_);
v___x_1148_ = v___x_1118_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_body_1135_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1150_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1148_);
lean_ctor_set(v___x_1114_, 0, v___x_1141_);
v___x_1150_ = v___x_1114_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
v_a_1128_ = v___x_1150_;
goto v___jp_1127_;
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v_body_1135_);
lean_del_object(v___x_1123_);
lean_dec(v_snd_1121_);
lean_dec(v_fst_1120_);
lean_del_object(v___x_1118_);
lean_del_object(v___x_1114_);
lean_dec(v_fst_1112_);
lean_dec(v_a_1101_);
lean_dec(v_mvarId_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v___y_1096_);
v_a_1154_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1139_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1139_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec(v_a_1133_);
v___x_1164_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3);
lean_inc(v_mvarId_1100_);
v___x_1165_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1131_, v_mvarId_1100_, v___x_1164_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v___x_1167_; 
lean_dec_ref_known(v___x_1165_, 1);
if (v_isShared_1124_ == 0)
{
v___x_1167_ = v___x_1123_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_fst_1120_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_snd_1121_);
v___x_1167_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v___x_1167_);
v___x_1169_ = v___x_1118_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_fst_1116_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1169_);
v___x_1171_ = v___x_1114_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_fst_1112_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
v_a_1128_ = v___x_1171_;
goto v___jp_1127_;
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_del_object(v___x_1123_);
lean_dec(v_snd_1121_);
lean_dec(v_fst_1120_);
lean_del_object(v___x_1118_);
lean_dec(v_fst_1116_);
lean_del_object(v___x_1114_);
lean_dec(v_fst_1112_);
lean_dec(v_a_1101_);
lean_dec(v_mvarId_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v___y_1096_);
v_a_1175_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1165_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1165_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_del_object(v___x_1123_);
lean_dec(v_snd_1121_);
lean_dec(v_fst_1120_);
lean_del_object(v___x_1118_);
lean_dec(v_fst_1116_);
lean_del_object(v___x_1114_);
lean_dec(v_fst_1112_);
lean_dec(v_a_1101_);
lean_dec(v_mvarId_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v___y_1096_);
v_a_1183_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1132_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1132_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
v___jp_1127_:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_nat_add(v_a_1101_, v___x_1126_);
lean_dec(v_a_1101_);
v_a_1101_ = v___x_1129_;
v_b_1102_ = v_a_1128_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1095_ = stack[0].m_obj;
lean_object* v___y_1096_ = stack[1].m_obj;
lean_object* v___x_1097_ = stack[2].m_obj;
lean_object* v___x_1098_ = stack[3].m_obj;
lean_object* v_a_1099_ = stack[4].m_obj;
lean_object* v_mvarId_1100_ = stack[5].m_obj;
lean_object* v_a_1101_ = stack[6].m_obj;
lean_object* v_b_1102_ = stack[7].m_obj;
lean_object* v___y_1103_ = stack[8].m_obj;
lean_object* v___y_1104_ = stack[9].m_obj;
lean_object* v___y_1105_ = stack[10].m_obj;
lean_object* v___y_1106_ = stack[11].m_obj;
lean_object* v_res_1196_;
v_res_1196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v_upperBound_1095_, v___y_1096_, v___x_1097_, v___x_1098_, v_a_1099_, v_mvarId_1100_, v_a_1101_, v_b_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
stack->m_obj
 = v_res_1196_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___boxed(lean_object* v_upperBound_1197_, lean_object* v___y_1198_, lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v_a_1201_, lean_object* v_mvarId_1202_, lean_object* v_a_1203_, lean_object* v_b_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v_upperBound_1197_, v___y_1198_, v___x_1199_, v___x_1200_, v_a_1201_, v_mvarId_1202_, v_a_1203_, v_b_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___x_1200_);
lean_dec(v_upperBound_1197_);
return v_res_1210_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(size_t v_sz_1211_, size_t v_i_1212_, lean_object* v_bs_1213_){
_start:
{
uint8_t v___x_1214_; 
v___x_1214_ = lean_usize_dec_lt(v_i_1212_, v_sz_1211_);
if (v___x_1214_ == 0)
{
return v_bs_1213_;
}
else
{
lean_object* v_v_1215_; lean_object* v___x_1216_; lean_object* v_bs_x27_1217_; lean_object* v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
v_v_1215_ = lean_array_uget(v_bs_1213_, v_i_1212_);
v___x_1216_ = lean_unsigned_to_nat(0u);
v_bs_x27_1217_ = lean_array_uset(v_bs_1213_, v_i_1212_, v___x_1216_);
v___x_1218_ = l_Lean_mkFVar(v_v_1215_);
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = lean_usize_add(v_i_1212_, v___x_1219_);
v___x_1221_ = lean_array_uset(v_bs_x27_1217_, v_i_1212_, v___x_1218_);
v_i_1212_ = v___x_1220_;
v_bs_1213_ = v___x_1221_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1211_ = stack[0].m_num;
size_t v_i_1212_ = stack[1].m_num;
lean_object* v_bs_1213_ = stack[2].m_obj;
lean_object* v_res_1223_;
v_res_1223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_1211_, v_i_1212_, v_bs_1213_);
stack->m_obj
 = v_res_1223_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2___boxed(lean_object* v_sz_1224_, lean_object* v_i_1225_, lean_object* v_bs_1226_){
_start:
{
size_t v_sz_boxed_1227_; size_t v_i_boxed_1228_; lean_object* v_res_1229_; 
v_sz_boxed_1227_ = lean_unbox_usize(v_sz_1224_);
lean_dec(v_sz_1224_);
v_i_boxed_1228_ = lean_unbox_usize(v_i_1225_);
lean_dec(v_i_1225_);
v_res_1229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_boxed_1227_, v_i_boxed_1228_, v_bs_1226_);
return v_res_1229_;
}
}
lean_object* l_Lean_Meta_Grind_cases___lam__0(lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_mvarId_1237_, lean_object* v_fvarId_1238_, lean_object* v_indices_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_sz_1245_ = lean_array_size(v_indices_1239_);
v___x_1246_ = ((size_t)0ULL);
lean_inc_ref(v_indices_1239_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_1245_, v___x_1246_, v_indices_1239_);
v___x_1248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
lean_inc_ref(v_a_1235_);
lean_inc(v_fvarId_1238_);
lean_inc(v_mvarId_1237_);
v___x_1249_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_1237_, v___x_1248_, v_fvarId_1238_, v_a_1235_, v___x_1247_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v_lctx_1251_; lean_object* v_localInstances_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___y_1257_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v_lctx_1251_ = lean_ctor_get(v___y_1240_, 2);
v_localInstances_1252_ = lean_ctor_get(v___y_1240_, 3);
v___x_1253_ = 1;
lean_inc(v_fvarId_1238_);
lean_inc_ref(v_lctx_1251_);
v___x_1254_ = l_Lean_LocalContext_setKind(v_lctx_1251_, v_fvarId_1238_, v___x_1253_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_array_get_size(v_indices_1239_);
v___x_1300_ = lean_nat_dec_lt(v___x_1255_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_dec_ref(v_indices_1239_);
v___y_1257_ = v___x_1254_;
goto v___jp_1256_;
}
else
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_nat_dec_le(v___x_1299_, v___x_1299_);
if (v___x_1301_ == 0)
{
if (v___x_1300_ == 0)
{
lean_dec_ref(v_indices_1239_);
v___y_1257_ = v___x_1254_;
goto v___jp_1256_;
}
else
{
size_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_usize_of_nat(v___x_1299_);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_indices_1239_, v___x_1246_, v___x_1302_, v___x_1254_);
lean_dec_ref(v_indices_1239_);
v___y_1257_ = v___x_1303_;
goto v___jp_1256_;
}
}
else
{
size_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_usize_of_nat(v___x_1299_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_indices_1239_, v___x_1246_, v___x_1304_, v___x_1254_);
lean_dec_ref(v_indices_1239_);
v___y_1257_ = v___x_1305_;
goto v___jp_1256_;
}
}
v___jp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1258_ = l_Lean_mkAppN(v_a_1250_, v___x_1247_);
lean_dec_ref(v___x_1247_);
v___x_1259_ = l_Lean_mkFVar(v_fvarId_1238_);
v___x_1260_ = l_Lean_Expr_app___override(v___x_1258_, v___x_1259_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc_ref(v___x_1260_);
v___x_1261_ = lean_infer_type(v___x_1260_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = l_Lean_Meta_RecursorInfo_numMinors(v_a_1235_);
lean_dec_ref(v_a_1235_);
v___x_1264_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__1));
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v_a_1262_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1260_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
lean_inc(v_mvarId_1237_);
lean_inc_ref(v_localInstances_1252_);
v___x_1267_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v___x_1263_, v___y_1257_, v_localInstances_1252_, v___x_1263_, v_a_1236_, v_mvarId_1237_, v___x_1255_, v___x_1266_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___x_1263_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v_snd_1269_; lean_object* v_snd_1270_; lean_object* v_fst_1271_; lean_object* v_fst_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1281_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v_snd_1269_ = lean_ctor_get(v_a_1268_, 1);
v_snd_1270_ = lean_ctor_get(v_snd_1269_, 1);
lean_inc(v_snd_1270_);
v_fst_1271_ = lean_ctor_get(v_a_1268_, 0);
lean_inc(v_fst_1271_);
lean_dec(v_a_1268_);
v_fst_1272_ = lean_ctor_get(v_snd_1270_, 0);
lean_inc(v_fst_1272_);
lean_dec(v_snd_1270_);
v___x_1273_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1237_, v_fst_1271_, v___y_1241_);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1273_, 0);
lean_dec(v_unused_1282_);
v___x_1275_ = v___x_1273_;
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v___x_1273_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_array_to_list(v_fst_1272_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1277_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_mvarId_1237_);
v_a_1283_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1267_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1267_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___y_1257_);
lean_dec(v_mvarId_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
v_a_1291_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1261_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1261_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v___x_1247_);
lean_dec_ref(v_indices_1239_);
lean_dec(v_fvarId_1238_);
lean_dec(v_mvarId_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
v_a_1306_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1249_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1249_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_cases___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1235_ = stack[0].m_obj;
lean_object* v_a_1236_ = stack[1].m_obj;
lean_object* v_mvarId_1237_ = stack[2].m_obj;
lean_object* v_fvarId_1238_ = stack[3].m_obj;
lean_object* v_indices_1239_ = stack[4].m_obj;
lean_object* v___y_1240_ = stack[5].m_obj;
lean_object* v___y_1241_ = stack[6].m_obj;
lean_object* v___y_1242_ = stack[7].m_obj;
lean_object* v___y_1243_ = stack[8].m_obj;
lean_object* v_res_1314_;
v_res_1314_ = l_Lean_Meta_Grind_cases___lam__0(v_a_1235_, v_a_1236_, v_mvarId_1237_, v_fvarId_1238_, v_indices_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
stack->m_obj
 = v_res_1314_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0___boxed(lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_mvarId_1317_, lean_object* v_fvarId_1318_, lean_object* v_indices_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Meta_Grind_cases___lam__0(v_a_1315_, v_a_1316_, v_mvarId_1317_, v_fvarId_1318_, v_indices_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1325_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6));
v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8));
v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10));
v___x_1343_ = l_Lean_stringToMessageData(v___x_1342_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__15(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__14));
v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__17(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__16));
v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__19(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__18));
v___x_1355_ = l_Lean_stringToMessageData(v___x_1354_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__21(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__20));
v___x_1358_ = l_Lean_stringToMessageData(v___x_1357_);
return v___x_1358_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_1359_, lean_object* v_declHint_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_env_1365_; uint8_t v___x_1366_; 
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_st_ref_get(v___y_1361_);
v_env_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc_ref(v_env_1365_);
lean_dec(v___x_1364_);
v___x_1366_ = l_Lean_Name_isAnonymous(v_declHint_1360_);
if (v___x_1366_ == 0)
{
uint8_t v_isExporting_1367_; 
v_isExporting_1367_ = lean_ctor_get_uint8(v_env_1365_, sizeof(void*)*13);
if (v_isExporting_1367_ == 0)
{
lean_object* v___x_1368_; 
lean_dec_ref(v_env_1365_);
lean_dec(v_declHint_1360_);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v_msg_1359_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
lean_inc_ref(v_env_1365_);
v___x_1369_ = l_Lean_Environment_setExporting(v_env_1365_, v___x_1366_);
lean_inc(v_declHint_1360_);
lean_inc_ref(v___x_1369_);
v___x_1370_ = l_Lean_Environment_contains(v___x_1369_, v_declHint_1360_, v_isExporting_1367_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec_ref(v___x_1369_);
lean_dec_ref(v_env_1365_);
lean_dec(v_declHint_1360_);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_msg_1359_);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_c_1377_; lean_object* v___x_1378_; 
v___x_1372_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2);
v___x_1373_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5);
v___x_1374_ = l_Lean_Options_empty;
v___x_1375_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1369_);
lean_ctor_set(v___x_1375_, 1, v___x_1372_);
lean_ctor_set(v___x_1375_, 2, v___x_1373_);
lean_ctor_set(v___x_1375_, 3, v___x_1374_);
lean_inc(v_declHint_1360_);
v___x_1376_ = l_Lean_MessageData_ofConstName(v_declHint_1360_, v___x_1366_);
v_c_1377_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1377_, 0, v___x_1375_);
lean_ctor_set(v_c_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1365_, v_declHint_1360_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref(v_env_1365_);
lean_dec(v_declHint_1360_);
v___x_1379_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1);
v___x_1380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v_c_1377_);
v___x_1381_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = l_Lean_MessageData_note(v___x_1382_);
v___x_1384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_msg_1359_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
else
{
lean_object* v_val_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1442_; 
v_val_1386_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1388_ = v___x_1378_;
v_isShared_1389_ = v_isSharedCheck_1442_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_val_1386_);
lean_dec(v___x_1378_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1442_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v_modules_1391_; lean_object* v_moduleNames_1392_; lean_object* v_mod_1393_; uint8_t v___y_1395_; uint8_t v___x_1425_; 
v___x_1390_ = l_Lean_Environment_header(v_env_1365_);
lean_dec_ref(v_env_1365_);
v_modules_1391_ = lean_ctor_get(v___x_1390_, 3);
lean_inc_ref(v_modules_1391_);
v_moduleNames_1392_ = lean_ctor_get(v___x_1390_, 4);
lean_inc_ref(v_moduleNames_1392_);
lean_dec_ref(v___x_1390_);
v_mod_1393_ = lean_array_get(v___x_1363_, v_moduleNames_1392_, v_val_1386_);
lean_dec_ref(v_moduleNames_1392_);
v___x_1425_ = l_Lean_isPrivateName(v_declHint_1360_);
lean_dec(v_declHint_1360_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = lean_array_get_size(v_modules_1391_);
v___x_1427_ = lean_nat_dec_lt(v_val_1386_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_dec_ref(v_modules_1391_);
lean_dec(v_val_1386_);
v___y_1395_ = v___x_1425_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1428_; lean_object* v_toImport_1429_; uint8_t v_isExported_1430_; 
v___x_1428_ = lean_array_fget(v_modules_1391_, v_val_1386_);
lean_dec(v_val_1386_);
lean_dec_ref(v_modules_1391_);
v_toImport_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc_ref(v_toImport_1429_);
lean_dec(v___x_1428_);
v_isExported_1430_ = lean_ctor_get_uint8(v_toImport_1429_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1429_);
v___y_1395_ = v_isExported_1430_;
goto v___jp_1394_;
}
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec_ref(v_modules_1391_);
lean_del_object(v___x_1388_);
lean_dec(v_val_1386_);
v___x_1431_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_c_1377_);
v___x_1433_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__19);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = l_Lean_MessageData_ofName(v_mod_1393_);
v___x_1436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1434_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__21);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = l_Lean_MessageData_note(v___x_1438_);
v___x_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1440_, 0, v_msg_1359_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
v___jp_1394_:
{
if (v___y_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1396_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5);
v___x_1397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v_c_1377_);
v___x_1398_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7);
v___x_1399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1397_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v___x_1400_ = l_Lean_MessageData_ofName(v_mod_1393_);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9);
v___x_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = l_Lean_MessageData_note(v___x_1403_);
v___x_1405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_msg_1359_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set_tag(v___x_1388_, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1405_);
v___x_1407_ = v___x_1388_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1409_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v_c_1377_);
v___x_1411_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = l_Lean_MessageData_ofName(v_mod_1393_);
lean_inc_ref(v___x_1413_);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__15);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v___x_1413_);
v___x_1418_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__17);
v___x_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1417_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = l_Lean_MessageData_note(v___x_1419_);
v___x_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1421_, 0, v_msg_1359_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set_tag(v___x_1388_, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1421_);
v___x_1423_ = v___x_1388_;
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
}
}
}
}
}
else
{
lean_object* v___x_1443_; 
lean_dec_ref(v_env_1365_);
lean_dec(v_declHint_1360_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_msg_1359_);
return v___x_1443_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1359_ = stack[0].m_obj;
lean_object* v_declHint_1360_ = stack[1].m_obj;
lean_object* v___y_1361_ = stack[2].m_obj;
lean_object* v_res_1444_;
v_res_1444_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1359_, v_declHint_1360_, v___y_1361_);
stack->m_obj
 = v_res_1444_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1445_, lean_object* v_declHint_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1445_, v_declHint_1446_, v___y_1447_);
lean_dec(v___y_1447_);
return v_res_1449_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(lean_object* v_msg_1450_, lean_object* v_declHint_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1467_; 
v___x_1457_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1450_, v_declHint_1451_, v___y_1455_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1467_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1467_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1462_ = l_Lean_unknownIdentifierMessageTag;
v___x_1463_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v_a_1458_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1463_);
v___x_1465_ = v___x_1460_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1450_ = stack[0].m_obj;
lean_object* v_declHint_1451_ = stack[1].m_obj;
lean_object* v___y_1452_ = stack[2].m_obj;
lean_object* v___y_1453_ = stack[3].m_obj;
lean_object* v___y_1454_ = stack[4].m_obj;
lean_object* v___y_1455_ = stack[5].m_obj;
lean_object* v_res_1468_;
v_res_1468_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_1450_, v_declHint_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
stack->m_obj
 = v_res_1468_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9___boxed(lean_object* v_msg_1469_, lean_object* v_declHint_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_1469_, v_declHint_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1476_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(lean_object* v_msgData_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v_env_1484_; uint8_t v___x_1485_; lean_object* v_env_1486_; lean_object* v___x_1487_; lean_object* v_toCold_1488_; lean_object* v_mctx_1489_; lean_object* v_lctx_1490_; lean_object* v_options_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1483_ = lean_st_ref_get(v___y_1481_);
v_env_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc_ref(v_env_1484_);
lean_dec(v___x_1483_);
v___x_1485_ = 0;
v_env_1486_ = l_Lean_Environment_setRecordingDeps(v_env_1484_, v___x_1485_);
v___x_1487_ = lean_st_ref_get(v___y_1479_);
v_toCold_1488_ = lean_ctor_get(v___y_1480_, 0);
v_mctx_1489_ = lean_ctor_get(v___x_1487_, 0);
lean_inc_ref(v_mctx_1489_);
lean_dec(v___x_1487_);
v_lctx_1490_ = lean_ctor_get(v___y_1478_, 2);
v_options_1491_ = lean_ctor_get(v_toCold_1488_, 2);
lean_inc_ref(v_options_1491_);
lean_inc_ref(v_lctx_1490_);
v___x_1492_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1492_, 0, v_env_1486_);
lean_ctor_set(v___x_1492_, 1, v_mctx_1489_);
lean_ctor_set(v___x_1492_, 2, v_lctx_1490_);
lean_ctor_set(v___x_1492_, 3, v_options_1491_);
v___x_1493_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
lean_ctor_set(v___x_1493_, 1, v_msgData_1477_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1477_ = stack[0].m_obj;
lean_object* v___y_1478_ = stack[1].m_obj;
lean_object* v___y_1479_ = stack[2].m_obj;
lean_object* v___y_1480_ = stack[3].m_obj;
lean_object* v___y_1481_ = stack[4].m_obj;
lean_object* v_res_1495_;
v_res_1495_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msgData_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
stack->m_obj
 = v_res_1495_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16___boxed(lean_object* v_msgData_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msgData_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1502_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(lean_object* v_msg_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_ref_1509_; lean_object* v___x_1510_; lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1519_; 
v_ref_1509_ = lean_ctor_get(v___y_1506_, 2);
v___x_1510_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msg_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1517_; 
lean_inc(v_ref_1509_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_ref_1509_);
lean_ctor_set(v___x_1515_, 1, v_a_1511_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set_tag(v___x_1513_, 1);
lean_ctor_set(v___x_1513_, 0, v___x_1515_);
v___x_1517_ = v___x_1513_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1503_ = stack[0].m_obj;
lean_object* v___y_1504_ = stack[1].m_obj;
lean_object* v___y_1505_ = stack[2].m_obj;
lean_object* v___y_1506_ = stack[3].m_obj;
lean_object* v___y_1507_ = stack[4].m_obj;
lean_object* v_res_1520_;
v_res_1520_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
stack->m_obj
 = v_res_1520_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_msg_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1527_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(lean_object* v_ref_1528_, lean_object* v_msg_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_toCold_1535_; lean_object* v_currRecDepth_1536_; lean_object* v_ref_1537_; uint16_t v_optionFlags_1538_; uint8_t v_suppressElabErrors_1539_; uint8_t v_isRecordingDeps_1540_; lean_object* v_ref_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_toCold_1535_ = lean_ctor_get(v___y_1532_, 0);
v_currRecDepth_1536_ = lean_ctor_get(v___y_1532_, 1);
v_ref_1537_ = lean_ctor_get(v___y_1532_, 2);
v_optionFlags_1538_ = lean_ctor_get_uint16(v___y_1532_, sizeof(void*)*3);
v_suppressElabErrors_1539_ = lean_ctor_get_uint8(v___y_1532_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1540_ = lean_ctor_get_uint8(v___y_1532_, sizeof(void*)*3 + 3);
v_ref_1541_ = l_Lean_replaceRef(v_ref_1528_, v_ref_1537_);
lean_inc(v_currRecDepth_1536_);
lean_inc_ref(v_toCold_1535_);
v___x_1542_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1542_, 0, v_toCold_1535_);
lean_ctor_set(v___x_1542_, 1, v_currRecDepth_1536_);
lean_ctor_set(v___x_1542_, 2, v_ref_1541_);
lean_ctor_set_uint16(v___x_1542_, sizeof(void*)*3, v_optionFlags_1538_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*3 + 2, v_suppressElabErrors_1539_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*3 + 3, v_isRecordingDeps_1540_);
v___x_1543_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1529_, v___y_1530_, v___y_1531_, v___x_1542_, v___y_1533_);
lean_dec_ref_known(v___x_1542_, 3);
return v___x_1543_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1528_ = stack[0].m_obj;
lean_object* v_msg_1529_ = stack[1].m_obj;
lean_object* v___y_1530_ = stack[2].m_obj;
lean_object* v___y_1531_ = stack[3].m_obj;
lean_object* v___y_1532_ = stack[4].m_obj;
lean_object* v___y_1533_ = stack[5].m_obj;
lean_object* v_res_1544_;
v_res_1544_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1528_, v_msg_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
stack->m_obj
 = v_res_1544_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg___boxed(lean_object* v_ref_1545_, lean_object* v_msg_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1545_, v_msg_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v_ref_1545_);
return v_res_1552_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_ref_1553_, lean_object* v_msg_1554_, lean_object* v_declHint_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v_a_1562_; lean_object* v___x_1563_; 
v___x_1561_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_1554_, v_declHint_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1561_);
v___x_1563_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1553_, v_a_1562_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1563_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1553_ = stack[0].m_obj;
lean_object* v_msg_1554_ = stack[1].m_obj;
lean_object* v_declHint_1555_ = stack[2].m_obj;
lean_object* v___y_1556_ = stack[3].m_obj;
lean_object* v___y_1557_ = stack[4].m_obj;
lean_object* v___y_1558_ = stack[5].m_obj;
lean_object* v___y_1559_ = stack[6].m_obj;
lean_object* v_res_1564_;
v_res_1564_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1553_, v_msg_1554_, v_declHint_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
stack->m_obj
 = v_res_1564_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1565_, lean_object* v_msg_1566_, lean_object* v_declHint_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1565_, v_msg_1566_, v_declHint_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v_ref_1565_);
return v_res_1573_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1576_ = l_Lean_stringToMessageData(v___x_1575_);
return v___x_1576_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1577_, lean_object* v_constName_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1584_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1585_ = 0;
lean_inc(v_constName_1578_);
v___x_1586_ = l_Lean_MessageData_ofConstName(v_constName_1578_, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1584_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1577_, v___x_1589_, v_constName_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
return v___x_1590_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1577_ = stack[0].m_obj;
lean_object* v_constName_1578_ = stack[1].m_obj;
lean_object* v___y_1579_ = stack[2].m_obj;
lean_object* v___y_1580_ = stack[3].m_obj;
lean_object* v___y_1581_ = stack[4].m_obj;
lean_object* v___y_1582_ = stack[5].m_obj;
lean_object* v_res_1591_;
v_res_1591_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1577_, v_constName_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
stack->m_obj
 = v_res_1591_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1592_, lean_object* v_constName_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1592_, v_constName_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v_ref_1592_);
return v_res_1599_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(lean_object* v_constName_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_ref_1606_; lean_object* v___x_1607_; 
v_ref_1606_ = lean_ctor_get(v___y_1603_, 2);
v___x_1607_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1606_, v_constName_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
return v___x_1607_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1600_ = stack[0].m_obj;
lean_object* v___y_1601_ = stack[1].m_obj;
lean_object* v___y_1602_ = stack[2].m_obj;
lean_object* v___y_1603_ = stack[3].m_obj;
lean_object* v___y_1604_ = stack[4].m_obj;
lean_object* v_res_1608_;
v_res_1608_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
stack->m_obj
 = v_res_1608_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
return v_res_1615_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(lean_object* v_constName_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; lean_object* v_env_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; 
v___x_1622_ = lean_st_ref_get(v___y_1620_);
v_env_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc_ref(v_env_1623_);
lean_dec(v___x_1622_);
v___x_1624_ = 0;
lean_inc(v_constName_1616_);
v___x_1625_ = l_Lean_Environment_find_x3f(v_env_1623_, v_constName_1616_, v___x_1624_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
return v___x_1626_;
}
else
{
lean_object* v_val_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec(v_constName_1616_);
v_val_1627_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1625_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_val_1627_);
lean_dec(v___x_1625_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 0);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_val_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1616_ = stack[0].m_obj;
lean_object* v___y_1617_ = stack[1].m_obj;
lean_object* v___y_1618_ = stack[2].m_obj;
lean_object* v___y_1619_ = stack[3].m_obj;
lean_object* v___y_1620_ = stack[4].m_obj;
lean_object* v_res_1635_;
v_res_1635_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(v_constName_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
stack->m_obj
 = v_res_1635_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0___boxed(lean_object* v_constName_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(v_constName_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1642_;
}
}
lean_object* l_Lean_Meta_Grind_cases___lam__1(lean_object* v_mvarId_1649_, lean_object* v_e_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; 
lean_inc(v_mvarId_1649_);
v___x_1656_ = l_Lean_MVarId_getTag(v_mvarId_1649_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
lean_inc_ref(v_e_1650_);
v___x_1658_ = lean_infer_type(v_e_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
v___x_1660_ = lean_whnf(v_a_1659_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1662_ = l_Lean_Expr_getAppFn(v_a_1661_);
if (lean_obj_tag(v___x_1662_) == 4)
{
lean_object* v_declName_1663_; lean_object* v___x_1664_; 
v_declName_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc_n(v_declName_1663_, 2);
lean_dec_ref_known(v___x_1662_, 2);
v___x_1664_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(v_declName_1663_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
if (lean_obj_tag(v_a_1665_) == 5)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec_ref_known(v_a_1665_, 1);
v___x_1666_ = l_Lean_mkCasesOnName(v_declName_1663_);
v___x_1667_ = lean_box(0);
v___x_1668_ = l_Lean_Meta_mkRecursorInfo(v___x_1666_, v___x_1667_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = l_Lean_Meta_RecursorInfo_numIndices(v_a_1669_);
v___x_1672_ = lean_nat_dec_lt(v___x_1670_, v___x_1671_);
lean_dec(v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
lean_inc_ref(v_e_1650_);
v___x_1673_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(v_e_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v_mvarId_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; uint8_t v___x_1697_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v___x_1697_ = lean_unbox(v_a_1674_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
lean_inc_ref(v_e_1650_);
v___x_1698_ = l_Lean_Meta_isProof(v_e_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; uint8_t v___x_1700_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1700_ = lean_unbox(v_a_1699_);
lean_dec(v_a_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__1));
v___x_1702_ = l_Lean_Core_mkFreshUserName(v___x_1701_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__3));
v___x_1705_ = l_Lean_MVarId_assertExt(v_mvarId_1649_, v_a_1703_, v_a_1661_, v_e_1650_, v___x_1704_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
v_mvarId_1676_ = v_a_1706_;
v___y_1677_ = v___y_1651_;
v___y_1678_ = v___y_1652_;
v___y_1679_ = v___y_1653_;
v___y_1680_ = v___y_1654_;
goto v___jp_1675_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_a_1674_);
lean_dec(v_a_1669_);
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
v_a_1707_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1705_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1705_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_a_1674_);
lean_dec(v_a_1669_);
lean_dec(v_a_1661_);
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_e_1650_);
lean_dec(v_mvarId_1649_);
v_a_1715_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1702_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1702_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__1));
v___x_1724_ = l_Lean_Core_mkFreshUserName(v___x_1723_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = l_Lean_MVarId_assert(v_mvarId_1649_, v_a_1725_, v_a_1661_, v_e_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v_mvarId_1676_ = v_a_1727_;
v___y_1677_ = v___y_1651_;
v___y_1678_ = v___y_1652_;
v___y_1679_ = v___y_1653_;
v___y_1680_ = v___y_1654_;
goto v___jp_1675_;
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec(v_a_1674_);
lean_dec(v_a_1669_);
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
v_a_1728_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1726_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_a_1674_);
lean_dec(v_a_1669_);
lean_dec(v_a_1661_);
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_e_1650_);
lean_dec(v_mvarId_1649_);
v_a_1736_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1724_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1724_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v_a_1674_);
lean_dec(v_a_1669_);
lean_dec(v_a_1661_);
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_e_1650_);
lean_dec(v_mvarId_1649_);
v_a_1744_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1698_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1698_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v_a_1674_);
lean_dec(v_a_1661_);
v___x_1752_ = l_Lean_Expr_fvarId_x21(v_e_1650_);
lean_dec_ref(v_e_1650_);
v___x_1753_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__0));
v___x_1754_ = l_Lean_Meta_Grind_cases___lam__0(v_a_1669_, v_a_1657_, v_mvarId_1649_, v___x_1752_, v___x_1753_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v___x_1754_;
}
v___jp_1675_:
{
uint8_t v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_unbox(v_a_1674_);
lean_dec(v_a_1674_);
v___x_1682_ = l_Lean_Meta_intro1Core(v_mvarId_1676_, v___x_1681_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v_fst_1684_; lean_object* v_snd_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1682_, 1);
v_fst_1684_ = lean_ctor_get(v_a_1683_, 0);
lean_inc(v_fst_1684_);
v_snd_1685_ = lean_ctor_get(v_a_1683_, 1);
lean_inc_n(v_snd_1685_, 2);
lean_dec(v_a_1683_);
v___x_1686_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__0));
v___x_1687_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__0___boxed), 10, 5);
lean_closure_set(v___x_1687_, 0, v_a_1669_);
lean_closure_set(v___x_1687_, 1, v_a_1657_);
lean_closure_set(v___x_1687_, 2, v_snd_1685_);
lean_closure_set(v___x_1687_, 3, v_fst_1684_);
lean_closure_set(v___x_1687_, 4, v___x_1686_);
v___x_1688_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_snd_1685_, v___x_1687_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v___x_1688_;
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_a_1669_);
lean_dec(v_a_1657_);
v_a_1689_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1682_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1682_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_a_1669_);
lean_dec(v_a_1661_);
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_e_1650_);
lean_dec(v_mvarId_1649_);
v_a_1755_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1673_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1673_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
lean_object* v___x_1763_; 
lean_dec(v_a_1661_);
v___x_1763_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1649_, v_e_1650_, v___x_1667_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v_mvarId_1765_; lean_object* v_indicesFVarIds_1766_; lean_object* v_fvarId_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v_mvarId_1765_ = lean_ctor_get(v_a_1764_, 0);
lean_inc_n(v_mvarId_1765_, 2);
v_indicesFVarIds_1766_ = lean_ctor_get(v_a_1764_, 1);
lean_inc_ref(v_indicesFVarIds_1766_);
v_fvarId_1767_ = lean_ctor_get(v_a_1764_, 2);
lean_inc(v_fvarId_1767_);
lean_dec(v_a_1764_);
v___x_1768_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__0___boxed), 10, 5);
lean_closure_set(v___x_1768_, 0, v_a_1669_);
lean_closure_set(v___x_1768_, 1, v_a_1657_);
lean_closure_set(v___x_1768_, 2, v_mvarId_1765_);
lean_closure_set(v___x_1768_, 3, v_fvarId_1767_);
lean_closure_set(v___x_1768_, 4, v_indicesFVarIds_1766_);
v___x_1769_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_1765_, v___x_1768_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v___x_1769_;
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v_a_1669_);
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
v_a_1770_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1763_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1763_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_a_1661_);
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_e_1650_);
lean_dec(v_mvarId_1649_);
v_a_1778_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1668_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1668_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v___x_1786_; 
lean_dec(v_a_1665_);
lean_dec(v_declName_1663_);
lean_dec(v_a_1657_);
v___x_1786_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_1649_, v_e_1650_, v_a_1661_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v___x_1786_;
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_declName_1663_);
lean_dec(v_a_1661_);
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_e_1650_);
lean_dec(v_mvarId_1649_);
v_a_1787_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1664_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1664_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v___x_1795_; 
lean_dec_ref(v___x_1662_);
lean_dec(v_a_1657_);
v___x_1795_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_1649_, v_e_1650_, v_a_1661_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v___x_1795_;
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_e_1650_);
lean_dec(v_mvarId_1649_);
v_a_1796_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1660_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1660_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v_a_1657_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_e_1650_);
lean_dec(v_mvarId_1649_);
v_a_1804_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1658_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1658_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_e_1650_);
lean_dec(v_mvarId_1649_);
v_a_1812_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1656_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1656_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_cases___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1649_ = stack[0].m_obj;
lean_object* v_e_1650_ = stack[1].m_obj;
lean_object* v___y_1651_ = stack[2].m_obj;
lean_object* v___y_1652_ = stack[3].m_obj;
lean_object* v___y_1653_ = stack[4].m_obj;
lean_object* v___y_1654_ = stack[5].m_obj;
lean_object* v_res_1820_;
v_res_1820_ = l_Lean_Meta_Grind_cases___lam__1(v_mvarId_1649_, v_e_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
stack->m_obj
 = v_res_1820_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1___boxed(lean_object* v_mvarId_1821_, lean_object* v_e_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Meta_Grind_cases___lam__1(v_mvarId_1821_, v_e_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
return v_res_1828_;
}
}
lean_object* l_Lean_Meta_Grind_cases(lean_object* v_mvarId_1829_, lean_object* v_e_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v___f_1836_; lean_object* v___x_1837_; 
lean_inc(v_mvarId_1829_);
v___f_1836_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1836_, 0, v_mvarId_1829_);
lean_closure_set(v___f_1836_, 1, v_e_1830_);
v___x_1837_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_1829_, v___f_1836_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
return v___x_1837_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_cases_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1829_ = stack[0].m_obj;
lean_object* v_e_1830_ = stack[1].m_obj;
lean_object* v_a_1831_ = stack[2].m_obj;
lean_object* v_a_1832_ = stack[3].m_obj;
lean_object* v_a_1833_ = stack[4].m_obj;
lean_object* v_a_1834_ = stack[5].m_obj;
lean_object* v_res_1838_;
v_res_1838_ = l_Lean_Meta_Grind_cases(v_mvarId_1829_, v_e_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
stack->m_obj
 = v_res_1838_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___boxed(lean_object* v_mvarId_1839_, lean_object* v_e_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Meta_Grind_cases(v_mvarId_1839_, v_e_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
return v_res_1846_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(lean_object* v_mvarId_1847_, lean_object* v_val_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1847_, v_val_1848_, v___y_1850_);
return v___x_1854_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1847_ = stack[0].m_obj;
lean_object* v_val_1848_ = stack[1].m_obj;
lean_object* v___y_1849_ = stack[2].m_obj;
lean_object* v___y_1850_ = stack[3].m_obj;
lean_object* v___y_1851_ = stack[4].m_obj;
lean_object* v___y_1852_ = stack[5].m_obj;
lean_object* v_res_1855_;
v_res_1855_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(v_mvarId_1847_, v_val_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
stack->m_obj
 = v_res_1855_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___boxed(lean_object* v_mvarId_1856_, lean_object* v_val_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(v_mvarId_1856_, v_val_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
return v_res_1863_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(lean_object* v_upperBound_1864_, lean_object* v___y_1865_, lean_object* v___x_1866_, lean_object* v___x_1867_, lean_object* v_a_1868_, lean_object* v_mvarId_1869_, lean_object* v_inst_1870_, lean_object* v_R_1871_, lean_object* v_a_1872_, lean_object* v_b_1873_, lean_object* v_c_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v_upperBound_1864_, v___y_1865_, v___x_1866_, v___x_1867_, v_a_1868_, v_mvarId_1869_, v_a_1872_, v_b_1873_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1864_ = stack[0].m_obj;
lean_object* v___y_1865_ = stack[1].m_obj;
lean_object* v___x_1866_ = stack[2].m_obj;
lean_object* v___x_1867_ = stack[3].m_obj;
lean_object* v_a_1868_ = stack[4].m_obj;
lean_object* v_mvarId_1869_ = stack[5].m_obj;
lean_object* v_a_1872_ = stack[8].m_obj;
lean_object* v_b_1873_ = stack[9].m_obj;
lean_object* v___y_1875_ = stack[11].m_obj;
lean_object* v___y_1876_ = stack[12].m_obj;
lean_object* v___y_1877_ = stack[13].m_obj;
lean_object* v___y_1878_ = stack[14].m_obj;
lean_object* v_res_1881_;
v_res_1881_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(v_upperBound_1864_, v___y_1865_, v___x_1866_, v___x_1867_, v_a_1868_, v_mvarId_1869_, lean_box(0), lean_box(0), v_a_1872_, v_b_1873_, lean_box(0), v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
stack->m_obj
 = v_res_1881_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___boxed(lean_object* v_upperBound_1882_, lean_object* v___y_1883_, lean_object* v___x_1884_, lean_object* v___x_1885_, lean_object* v_a_1886_, lean_object* v_mvarId_1887_, lean_object* v_inst_1888_, lean_object* v_R_1889_, lean_object* v_a_1890_, lean_object* v_b_1891_, lean_object* v_c_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(v_upperBound_1882_, v___y_1883_, v___x_1884_, v___x_1885_, v_a_1886_, v_mvarId_1887_, v_inst_1888_, v_R_1889_, v_a_1890_, v_b_1891_, v_c_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___x_1885_);
lean_dec(v_upperBound_1882_);
return v_res_1898_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(lean_object* v_00_u03b1_1899_, lean_object* v_constName_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1900_ = stack[1].m_obj;
lean_object* v___y_1901_ = stack[2].m_obj;
lean_object* v___y_1902_ = stack[3].m_obj;
lean_object* v___y_1903_ = stack[4].m_obj;
lean_object* v___y_1904_ = stack[5].m_obj;
lean_object* v_res_1907_;
v_res_1907_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(lean_box(0), v_constName_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
stack->m_obj
 = v_res_1907_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1908_, lean_object* v_constName_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(v_00_u03b1_1908_, v_constName_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2(lean_object* v_00_u03b2_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(v_x_1917_, v_x_1918_, v_x_1919_);
return v___x_1920_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1921_, lean_object* v_ref_1922_, lean_object* v_constName_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1922_, v_constName_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1922_ = stack[1].m_obj;
lean_object* v_constName_1923_ = stack[2].m_obj;
lean_object* v___y_1924_ = stack[3].m_obj;
lean_object* v___y_1925_ = stack[4].m_obj;
lean_object* v___y_1926_ = stack[5].m_obj;
lean_object* v___y_1927_ = stack[6].m_obj;
lean_object* v_res_1930_;
v_res_1930_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(lean_box(0), v_ref_1922_, v_constName_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
stack->m_obj
 = v_res_1930_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1931_, lean_object* v_ref_1932_, lean_object* v_constName_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(v_00_u03b1_1931_, v_ref_1932_, v_constName_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v_ref_1932_);
return v_res_1939_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1940_, lean_object* v_x_1941_, size_t v_x_1942_, size_t v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_1941_, v_x_1942_, v_x_1943_, v_x_1944_, v_x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1941_ = stack[1].m_obj;
size_t v_x_1942_ = stack[2].m_num;
size_t v_x_1943_ = stack[3].m_num;
lean_object* v_x_1944_ = stack[4].m_obj;
lean_object* v_x_1945_ = stack[5].m_obj;
lean_object* v_res_1947_;
v_res_1947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(lean_box(0), v_x_1941_, v_x_1942_, v_x_1943_, v_x_1944_, v_x_1945_);
stack->m_obj
 = v_res_1947_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_){
_start:
{
size_t v_x_14372__boxed_1954_; size_t v_x_14373__boxed_1955_; lean_object* v_res_1956_; 
v_x_14372__boxed_1954_ = lean_unbox_usize(v_x_1950_);
lean_dec(v_x_1950_);
v_x_14373__boxed_1955_ = lean_unbox_usize(v_x_1951_);
lean_dec(v_x_1951_);
v_res_1956_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(v_00_u03b2_1948_, v_x_1949_, v_x_14372__boxed_1954_, v_x_14373__boxed_1955_, v_x_1952_, v_x_1953_);
return v_res_1956_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b1_1957_, lean_object* v_ref_1958_, lean_object* v_msg_1959_, lean_object* v_declHint_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1958_, v_msg_1959_, v_declHint_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1958_ = stack[1].m_obj;
lean_object* v_msg_1959_ = stack[2].m_obj;
lean_object* v_declHint_1960_ = stack[3].m_obj;
lean_object* v___y_1961_ = stack[4].m_obj;
lean_object* v___y_1962_ = stack[5].m_obj;
lean_object* v___y_1963_ = stack[6].m_obj;
lean_object* v___y_1964_ = stack[7].m_obj;
lean_object* v_res_1967_;
v_res_1967_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(lean_box(0), v_ref_1958_, v_msg_1959_, v_declHint_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
stack->m_obj
 = v_res_1967_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b1_1968_, lean_object* v_ref_1969_, lean_object* v_msg_1970_, lean_object* v_declHint_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(v_00_u03b1_1968_, v_ref_1969_, v_msg_1970_, v_declHint_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v_ref_1969_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_1978_, lean_object* v_n_1979_, lean_object* v_k_1980_, lean_object* v_v_1981_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(v_n_1979_, v_k_1980_, v_v_1981_);
return v___x_1982_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(lean_object* v_00_u03b2_1983_, size_t v_depth_1984_, lean_object* v_keys_1985_, lean_object* v_vals_1986_, lean_object* v_heq_1987_, lean_object* v_i_1988_, lean_object* v_entries_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_1984_, v_keys_1985_, v_vals_1986_, v_i_1988_, v_entries_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1984_ = stack[1].m_num;
lean_object* v_keys_1985_ = stack[2].m_obj;
lean_object* v_vals_1986_ = stack[3].m_obj;
lean_object* v_i_1988_ = stack[5].m_obj;
lean_object* v_entries_1989_ = stack[6].m_obj;
lean_object* v_res_1991_;
v_res_1991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(lean_box(0), v_depth_1984_, v_keys_1985_, v_vals_1986_, lean_box(0), v_i_1988_, v_entries_1989_);
stack->m_obj
 = v_res_1991_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1992_, lean_object* v_depth_1993_, lean_object* v_keys_1994_, lean_object* v_vals_1995_, lean_object* v_heq_1996_, lean_object* v_i_1997_, lean_object* v_entries_1998_){
_start:
{
size_t v_depth_boxed_1999_; lean_object* v_res_2000_; 
v_depth_boxed_1999_ = lean_unbox_usize(v_depth_1993_);
lean_dec(v_depth_1993_);
v_res_2000_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(v_00_u03b2_1992_, v_depth_boxed_1999_, v_keys_1994_, v_vals_1995_, v_heq_1996_, v_i_1997_, v_entries_1998_);
lean_dec_ref(v_vals_1995_);
lean_dec_ref(v_keys_1994_);
return v_res_2000_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(lean_object* v_msg_2001_, lean_object* v_declHint_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_2001_, v_declHint_2002_, v___y_2006_);
return v___x_2008_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2001_ = stack[0].m_obj;
lean_object* v_declHint_2002_ = stack[1].m_obj;
lean_object* v___y_2003_ = stack[2].m_obj;
lean_object* v___y_2004_ = stack[3].m_obj;
lean_object* v___y_2005_ = stack[4].m_obj;
lean_object* v___y_2006_ = stack[5].m_obj;
lean_object* v_res_2009_;
v_res_2009_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(v_msg_2001_, v_declHint_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
stack->m_obj
 = v_res_2009_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_2010_, lean_object* v_declHint_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(v_msg_2010_, v_declHint_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v_res_2017_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(lean_object* v_00_u03b1_2018_, lean_object* v_ref_2019_, lean_object* v_msg_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_2019_, v_msg_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2026_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2019_ = stack[1].m_obj;
lean_object* v_msg_2020_ = stack[2].m_obj;
lean_object* v___y_2021_ = stack[3].m_obj;
lean_object* v___y_2022_ = stack[4].m_obj;
lean_object* v___y_2023_ = stack[5].m_obj;
lean_object* v___y_2024_ = stack[6].m_obj;
lean_object* v_res_2027_;
v_res_2027_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(lean_box(0), v_ref_2019_, v_msg_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
stack->m_obj
 = v_res_2027_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2028_, lean_object* v_ref_2029_, lean_object* v_msg_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(v_00_u03b1_2028_, v_ref_2029_, v_msg_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v_ref_2029_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13(lean_object* v_00_u03b2_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(v_x_2038_, v_x_2039_, v_x_2040_, v_x_2041_);
return v___x_2042_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_2043_, lean_object* v_msg_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
return v___x_2050_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2044_ = stack[1].m_obj;
lean_object* v___y_2045_ = stack[2].m_obj;
lean_object* v___y_2046_ = stack[3].m_obj;
lean_object* v___y_2047_ = stack[4].m_obj;
lean_object* v___y_2048_ = stack[5].m_obj;
lean_object* v_res_2051_;
v_res_2051_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(lean_box(0), v_msg_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
stack->m_obj
 = v_res_2051_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b1_2052_, lean_object* v_msg_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(v_00_u03b1_2052_, v_msg_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2059_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases = _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
}
#ifdef __cplusplus
}
#endif
