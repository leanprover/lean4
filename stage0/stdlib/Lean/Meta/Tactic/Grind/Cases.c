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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13;
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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object* v_declName_45_){
_start:
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
v___x_47_ = l_Lean_NameSet_contains(v___x_46_, v_declName_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isBuiltinEagerCases___boxed(lean_object* v_declName_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_48_);
lean_dec(v_declName_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_51_, lean_object* v_i_52_, lean_object* v_k_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = lean_array_get_size(v_keys_51_);
v___x_55_ = lean_nat_dec_lt(v_i_52_, v___x_54_);
if (v___x_55_ == 0)
{
lean_dec(v_i_52_);
return v___x_55_;
}
else
{
lean_object* v_k_x27_56_; uint8_t v___x_57_; 
v_k_x27_56_ = lean_array_fget_borrowed(v_keys_51_, v_i_52_);
v___x_57_ = lean_name_eq(v_k_53_, v_k_x27_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_add(v_i_52_, v___x_58_);
lean_dec(v_i_52_);
v_i_52_ = v___x_59_;
goto _start;
}
else
{
lean_dec(v_i_52_);
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_61_, lean_object* v_i_62_, lean_object* v_k_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_keys_61_, v_i_62_, v_k_63_);
lean_dec(v_k_63_);
lean_dec_ref(v_keys_61_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(lean_object* v_x_66_, size_t v_x_67_, lean_object* v_x_68_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v_es_69_; lean_object* v___x_70_; size_t v___x_71_; size_t v___x_72_; lean_object* v_j_73_; lean_object* v___x_74_; 
v_es_69_ = lean_ctor_get(v_x_66_, 0);
v___x_70_ = lean_box(2);
v___x_71_ = ((size_t)31ULL);
v___x_72_ = lean_usize_land(v_x_67_, v___x_71_);
v_j_73_ = lean_usize_to_nat(v___x_72_);
v___x_74_ = lean_array_get_borrowed(v___x_70_, v_es_69_, v_j_73_);
lean_dec(v_j_73_);
switch(lean_obj_tag(v___x_74_))
{
case 0:
{
lean_object* v_key_75_; uint8_t v___x_76_; 
v_key_75_ = lean_ctor_get(v___x_74_, 0);
v___x_76_ = lean_name_eq(v_x_68_, v_key_75_);
return v___x_76_;
}
case 1:
{
lean_object* v_node_77_; size_t v___x_78_; size_t v___x_79_; 
v_node_77_ = lean_ctor_get(v___x_74_, 0);
v___x_78_ = ((size_t)5ULL);
v___x_79_ = lean_usize_shift_right(v_x_67_, v___x_78_);
v_x_66_ = v_node_77_;
v_x_67_ = v___x_79_;
goto _start;
}
default: 
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
}
else
{
lean_object* v_ks_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_ks_82_ = lean_ctor_get(v_x_66_, 0);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_ks_82_, v___x_83_, v_x_68_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
size_t v_x_122__boxed_88_; uint8_t v_res_89_; lean_object* v_r_90_; 
v_x_122__boxed_88_ = lean_unbox_usize(v_x_86_);
lean_dec(v_x_86_);
v_res_89_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_85_, v_x_122__boxed_88_, v_x_87_);
lean_dec(v_x_87_);
lean_dec_ref(v_x_85_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
uint64_t v___y_94_; 
if (lean_obj_tag(v_x_92_) == 0)
{
uint64_t v___x_97_; 
v___x_97_ = 1723ULL;
v___y_94_ = v___x_97_;
goto v___jp_93_;
}
else
{
uint64_t v_hash_98_; 
v_hash_98_ = lean_ctor_get_uint64(v_x_92_, sizeof(void*)*2);
v___y_94_ = v_hash_98_;
goto v___jp_93_;
}
v___jp_93_:
{
size_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_uint64_to_usize(v___y_94_);
v___x_96_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_91_, v___x_95_, v_x_92_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___boxed(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_99_, v_x_100_);
lean_dec(v_x_100_);
lean_dec_ref(v_x_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object* v_s_103_, lean_object* v_declName_104_){
_start:
{
uint8_t v___x_105_; 
v___x_105_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_s_103_, v_declName_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_contains___boxed(lean_object* v_s_106_, lean_object* v_declName_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Lean_Meta_Grind_CasesTypes_contains(v_s_106_, v_declName_107_);
lean_dec(v_declName_107_);
lean_dec_ref(v_s_106_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(lean_object* v_00_u03b2_110_, lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_111_, v_x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___boxed(lean_object* v_00_u03b2_114_, lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(v_00_u03b2_114_, v_x_115_, v_x_116_);
lean_dec(v_x_116_);
lean_dec_ref(v_x_115_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(lean_object* v_00_u03b2_119_, lean_object* v_x_120_, size_t v_x_121_, lean_object* v_x_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_120_, v_x_121_, v_x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_124_, lean_object* v_x_125_, lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
size_t v_x_189__boxed_128_; uint8_t v_res_129_; lean_object* v_r_130_; 
v_x_189__boxed_128_ = lean_unbox_usize(v_x_126_);
lean_dec(v_x_126_);
v_res_129_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(v_00_u03b2_124_, v_x_125_, v_x_189__boxed_128_, v_x_127_);
lean_dec(v_x_127_);
lean_dec_ref(v_x_125_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_131_, lean_object* v_keys_132_, lean_object* v_vals_133_, lean_object* v_heq_134_, lean_object* v_i_135_, lean_object* v_k_136_){
_start:
{
uint8_t v___x_137_; 
v___x_137_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_keys_132_, v_i_135_, v_k_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_138_, lean_object* v_keys_139_, lean_object* v_vals_140_, lean_object* v_heq_141_, lean_object* v_i_142_, lean_object* v_k_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(v_00_u03b2_138_, v_keys_139_, v_vals_140_, v_heq_141_, v_i_142_, v_k_143_);
lean_dec(v_k_143_);
lean_dec_ref(v_vals_140_);
lean_dec_ref(v_keys_139_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(lean_object* v_xs_146_, lean_object* v_v_147_, lean_object* v_i_148_){
_start:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_array_get_size(v_xs_146_);
v___x_150_ = lean_nat_dec_lt(v_i_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec(v_i_148_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_array_fget_borrowed(v_xs_146_, v_i_148_);
v___x_153_ = lean_name_eq(v___x_152_, v_v_147_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_i_148_, v___x_154_);
lean_dec(v_i_148_);
v_i_148_ = v___x_155_;
goto _start;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v_i_148_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_xs_158_, lean_object* v_v_159_, lean_object* v_i_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(v_xs_158_, v_v_159_, v_i_160_);
lean_dec(v_v_159_);
lean_dec_ref(v_xs_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(lean_object* v_xs_162_, lean_object* v_v_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(v_xs_162_, v_v_163_, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_166_, lean_object* v_v_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(v_xs_166_, v_v_167_);
lean_dec(v_v_167_);
lean_dec_ref(v_xs_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(lean_object* v_x_169_, size_t v_x_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v_es_172_; lean_object* v___x_173_; size_t v___x_174_; size_t v___x_175_; lean_object* v_j_176_; lean_object* v_entry_177_; 
v_es_172_ = lean_ctor_get(v_x_169_, 0);
v___x_173_ = lean_box(2);
v___x_174_ = ((size_t)31ULL);
v___x_175_ = lean_usize_land(v_x_170_, v___x_174_);
v_j_176_ = lean_usize_to_nat(v___x_175_);
v_entry_177_ = lean_array_get(v___x_173_, v_es_172_, v_j_176_);
switch(lean_obj_tag(v_entry_177_))
{
case 0:
{
lean_object* v_key_178_; uint8_t v___x_179_; 
v_key_178_ = lean_ctor_get(v_entry_177_, 0);
lean_inc(v_key_178_);
lean_dec_ref_known(v_entry_177_, 2);
v___x_179_ = lean_name_eq(v_x_171_, v_key_178_);
lean_dec(v_key_178_);
if (v___x_179_ == 0)
{
lean_dec(v_j_176_);
return v_x_169_;
}
else
{
lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
lean_inc_ref(v_es_172_);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_x_169_, 0);
lean_dec(v_unused_188_);
v___x_181_ = v_x_169_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_dec(v_x_169_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = lean_array_set(v_es_172_, v_j_176_, v___x_173_);
lean_dec(v_j_176_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_183_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
case 1:
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_223_; 
lean_inc_ref(v_es_172_);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; 
v_unused_224_ = lean_ctor_get(v_x_169_, 0);
lean_dec(v_unused_224_);
v___x_190_ = v_x_169_;
v_isShared_191_ = v_isSharedCheck_223_;
goto v_resetjp_189_;
}
else
{
lean_dec(v_x_169_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_223_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_node_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_222_; 
v_node_192_ = lean_ctor_get(v_entry_177_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_entry_177_);
if (v_isSharedCheck_222_ == 0)
{
v___x_194_ = v_entry_177_;
v_isShared_195_ = v_isSharedCheck_222_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_node_192_);
lean_dec(v_entry_177_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_222_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
size_t v___x_196_; lean_object* v_entries_197_; size_t v___x_198_; lean_object* v_newNode_199_; lean_object* v___x_200_; 
v___x_196_ = ((size_t)5ULL);
v_entries_197_ = lean_array_set(v_es_172_, v_j_176_, v___x_173_);
v___x_198_ = lean_usize_shift_right(v_x_170_, v___x_196_);
v_newNode_199_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_node_192_, v___x_198_, v_x_171_);
lean_inc_ref(v_newNode_199_);
v___x_200_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_202_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v_newNode_199_);
v___x_202_ = v___x_194_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_newNode_199_);
v___x_202_ = v_reuseFailAlloc_207_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_array_set(v_entries_197_, v_j_176_, v___x_202_);
lean_dec(v_j_176_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_203_);
v___x_205_ = v___x_190_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
else
{
lean_object* v_val_208_; lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_221_; 
lean_dec_ref(v_newNode_199_);
lean_del_object(v___x_194_);
v_val_208_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_200_, 1);
v_fst_209_ = lean_ctor_get(v_val_208_, 0);
v_snd_210_ = lean_ctor_get(v_val_208_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_val_208_);
if (v_isSharedCheck_221_ == 0)
{
v___x_212_ = v_val_208_;
v_isShared_213_ = v_isSharedCheck_221_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_snd_210_);
lean_inc(v_fst_209_);
lean_dec(v_val_208_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_221_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_fst_209_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_snd_210_);
v___x_215_ = v_reuseFailAlloc_220_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_array_set(v_entries_197_, v_j_176_, v___x_215_);
lean_dec(v_j_176_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_216_);
v___x_218_ = v___x_190_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_176_);
return v_x_169_;
}
}
}
else
{
lean_object* v_ks_225_; lean_object* v_vs_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_240_; 
v_ks_225_ = lean_ctor_get(v_x_169_, 0);
v_vs_226_ = lean_ctor_get(v_x_169_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_240_ == 0)
{
v___x_228_ = v_x_169_;
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_vs_226_);
lean_inc(v_ks_225_);
lean_dec(v_x_169_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; 
v___x_230_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(v_ks_225_, v_x_171_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_232_; 
if (v_isShared_229_ == 0)
{
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_ks_225_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_vs_226_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
else
{
lean_object* v_val_234_; lean_object* v_keys_x27_235_; lean_object* v_vals_x27_236_; lean_object* v___x_238_; 
v_val_234_ = lean_ctor_get(v___x_230_, 0);
lean_inc_n(v_val_234_, 2);
lean_dec_ref_known(v___x_230_, 1);
v_keys_x27_235_ = l_Array_eraseIdx___redArg(v_ks_225_, v_val_234_);
v_vals_x27_236_ = l_Array_eraseIdx___redArg(v_vs_226_, v_val_234_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v_vals_x27_236_);
lean_ctor_set(v___x_228_, 0, v_keys_x27_235_);
v___x_238_ = v___x_228_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_keys_x27_235_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_vals_x27_236_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
size_t v_x_178__boxed_244_; lean_object* v_res_245_; 
v_x_178__boxed_244_ = lean_unbox_usize(v_x_242_);
lean_dec(v_x_242_);
v_res_245_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_241_, v_x_178__boxed_244_, v_x_243_);
lean_dec(v_x_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
uint64_t v___y_249_; 
if (lean_obj_tag(v_x_247_) == 0)
{
uint64_t v___x_252_; 
v___x_252_ = 1723ULL;
v___y_249_ = v___x_252_;
goto v___jp_248_;
}
else
{
uint64_t v_hash_253_; 
v_hash_253_ = lean_ctor_get_uint64(v_x_247_, sizeof(void*)*2);
v___y_249_ = v_hash_253_;
goto v___jp_248_;
}
v___jp_248_:
{
size_t v_h_250_; lean_object* v___x_251_; 
v_h_250_ = lean_uint64_to_usize(v___y_249_);
v___x_251_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_246_, v_h_250_, v_x_247_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg___boxed(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_x_254_, v_x_255_);
lean_dec(v_x_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase(lean_object* v_s_257_, lean_object* v_declName_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_s_257_, v_declName_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase___boxed(lean_object* v_s_260_, lean_object* v_declName_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Meta_Grind_CasesTypes_erase(v_s_260_, v_declName_261_);
lean_dec(v_declName_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(lean_object* v_00_u03b2_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_x_264_, v_x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___boxed(lean_object* v_00_u03b2_267_, lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(v_00_u03b2_267_, v_x_268_, v_x_269_);
lean_dec(v_x_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(lean_object* v_00_u03b2_271_, lean_object* v_x_272_, size_t v_x_273_, lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_272_, v_x_273_, v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_276_, lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
size_t v_x_338__boxed_280_; lean_object* v_res_281_; 
v_x_338__boxed_280_ = lean_unbox_usize(v_x_278_);
lean_dec(v_x_278_);
v_res_281_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(v_00_u03b2_276_, v_x_277_, v_x_338__boxed_280_, v_x_279_);
lean_dec(v_x_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_282_, lean_object* v_vals_283_, lean_object* v_i_284_, lean_object* v_k_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_array_get_size(v_keys_282_);
v___x_287_ = lean_nat_dec_lt(v_i_284_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
lean_dec(v_i_284_);
v___x_288_ = lean_box(0);
return v___x_288_;
}
else
{
lean_object* v_k_x27_289_; uint8_t v___x_290_; 
v_k_x27_289_ = lean_array_fget_borrowed(v_keys_282_, v_i_284_);
v___x_290_ = lean_name_eq(v_k_285_, v_k_x27_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_i_284_, v___x_291_);
lean_dec(v_i_284_);
v_i_284_ = v___x_292_;
goto _start;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_array_fget_borrowed(v_vals_283_, v_i_284_);
lean_dec(v_i_284_);
lean_inc(v___x_294_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_296_, lean_object* v_vals_297_, lean_object* v_i_298_, lean_object* v_k_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_296_, v_vals_297_, v_i_298_, v_k_299_);
lean_dec(v_k_299_);
lean_dec_ref(v_vals_297_);
lean_dec_ref(v_keys_296_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_301_, size_t v_x_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_es_304_; lean_object* v___x_305_; size_t v___x_306_; size_t v___x_307_; lean_object* v_j_308_; lean_object* v___x_309_; 
v_es_304_ = lean_ctor_get(v_x_301_, 0);
v___x_305_ = lean_box(2);
v___x_306_ = ((size_t)31ULL);
v___x_307_ = lean_usize_land(v_x_302_, v___x_306_);
v_j_308_ = lean_usize_to_nat(v___x_307_);
v___x_309_ = lean_array_get_borrowed(v___x_305_, v_es_304_, v_j_308_);
lean_dec(v_j_308_);
switch(lean_obj_tag(v___x_309_))
{
case 0:
{
lean_object* v_key_310_; lean_object* v_val_311_; uint8_t v___x_312_; 
v_key_310_ = lean_ctor_get(v___x_309_, 0);
v_val_311_ = lean_ctor_get(v___x_309_, 1);
v___x_312_ = lean_name_eq(v_x_303_, v_key_310_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_box(0);
return v___x_313_;
}
else
{
lean_object* v___x_314_; 
lean_inc(v_val_311_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v_val_311_);
return v___x_314_;
}
}
case 1:
{
lean_object* v_node_315_; size_t v___x_316_; size_t v___x_317_; 
v_node_315_ = lean_ctor_get(v___x_309_, 0);
v___x_316_ = ((size_t)5ULL);
v___x_317_ = lean_usize_shift_right(v_x_302_, v___x_316_);
v_x_301_ = v_node_315_;
v_x_302_ = v___x_317_;
goto _start;
}
default: 
{
lean_object* v___x_319_; 
v___x_319_ = lean_box(0);
return v___x_319_;
}
}
}
else
{
lean_object* v_ks_320_; lean_object* v_vs_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_ks_320_ = lean_ctor_get(v_x_301_, 0);
v_vs_321_ = lean_ctor_get(v_x_301_, 1);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_320_, v_vs_321_, v___x_322_, v_x_303_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
size_t v_x_138__boxed_327_; lean_object* v_res_328_; 
v_x_138__boxed_327_ = lean_unbox_usize(v_x_325_);
lean_dec(v_x_325_);
v_res_328_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_324_, v_x_138__boxed_327_, v_x_326_);
lean_dec(v_x_326_);
lean_dec_ref(v_x_324_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
uint64_t v___y_332_; 
if (lean_obj_tag(v_x_330_) == 0)
{
uint64_t v___x_335_; 
v___x_335_ = 1723ULL;
v___y_332_ = v___x_335_;
goto v___jp_331_;
}
else
{
uint64_t v_hash_336_; 
v_hash_336_ = lean_ctor_get_uint64(v_x_330_, sizeof(void*)*2);
v___y_332_ = v_hash_336_;
goto v___jp_331_;
}
v___jp_331_:
{
size_t v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_uint64_to_usize(v___y_332_);
v___x_334_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_329_, v___x_333_, v_x_330_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg___boxed(lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_x_337_, v_x_338_);
lean_dec(v_x_338_);
lean_dec_ref(v_x_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f(lean_object* v_s_340_, lean_object* v_declName_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_340_, v_declName_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f___boxed(lean_object* v_s_343_, lean_object* v_declName_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Meta_Grind_CasesTypes_find_x3f(v_s_343_, v_declName_344_);
lean_dec(v_declName_344_);
lean_dec_ref(v_s_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(lean_object* v_00_u03b2_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_x_347_, v_x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(v_00_u03b2_350_, v_x_351_, v_x_352_);
lean_dec(v_x_352_);
lean_dec_ref(v_x_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_354_, lean_object* v_x_355_, size_t v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_355_, v_x_356_, v_x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
size_t v_x_211__boxed_363_; lean_object* v_res_364_; 
v_x_211__boxed_363_ = lean_unbox_usize(v_x_361_);
lean_dec(v_x_361_);
v_res_364_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(v_00_u03b2_359_, v_x_360_, v_x_211__boxed_363_, v_x_362_);
lean_dec(v_x_362_);
lean_dec_ref(v_x_360_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_365_, lean_object* v_keys_366_, lean_object* v_vals_367_, lean_object* v_heq_368_, lean_object* v_i_369_, lean_object* v_k_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_366_, v_vals_367_, v_i_369_, v_k_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_372_, lean_object* v_keys_373_, lean_object* v_vals_374_, lean_object* v_heq_375_, lean_object* v_i_376_, lean_object* v_k_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_372_, v_keys_373_, v_vals_374_, v_heq_375_, v_i_376_, v_k_377_);
lean_dec(v_k_377_);
lean_dec_ref(v_vals_374_);
lean_dec_ref(v_keys_373_);
return v_res_378_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_isEagerSplit(lean_object* v_s_379_, lean_object* v_declName_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_379_, v_declName_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
uint8_t v___x_382_; 
v___x_382_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_380_);
return v___x_382_;
}
else
{
lean_object* v_val_383_; uint8_t v___x_384_; 
v_val_383_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v___x_381_, 1);
v___x_384_ = lean_unbox(v_val_383_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
lean_dec(v_val_383_);
v___x_385_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_380_);
return v___x_385_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = lean_unbox(v_val_383_);
lean_dec(v_val_383_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isEagerSplit___boxed(lean_object* v_s_387_, lean_object* v_declName_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lean_Meta_Grind_CasesTypes_isEagerSplit(v_s_387_, v_declName_388_);
lean_dec(v_declName_388_);
lean_dec_ref(v_s_387_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object* v_s_391_, lean_object* v_declName_392_){
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
uint8_t v___x_395_; 
lean_dec_ref_known(v___x_393_, 1);
v___x_395_ = 1;
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isSplit___boxed(lean_object* v_s_396_, lean_object* v_declName_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_s_396_, v_declName_397_);
lean_dec(v_declName_397_);
lean_dec_ref(v_s_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(lean_object* v_declName_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; lean_object* v_env_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_st_ref_get(v___y_401_);
v_env_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc_ref(v_env_404_);
lean_dec(v___x_403_);
v___x_405_ = l_Lean_isInductiveCore_x3f(v_env_404_, v_declName_400_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg___boxed(lean_object* v_declName_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_407_, v___y_408_);
lean_dec(v___y_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(lean_object* v_declName_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_411_, v___y_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___boxed(lean_object* v_declName_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(v_declName_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object* v_declName_421_, uint8_t v_eager_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_448_; 
lean_inc(v_declName_421_);
v___x_426_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_421_, v_a_424_);
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_448_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_448_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_448_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
if (lean_obj_tag(v_a_427_) == 1)
{
lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_445_; 
v_val_436_ = lean_ctor_get(v_a_427_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_445_ == 0)
{
v___x_438_ = v_a_427_;
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_dec(v_a_427_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
uint8_t v_isRec_440_; 
v_isRec_440_ = lean_ctor_get_uint8(v_val_436_, sizeof(void*)*6);
lean_dec(v_val_436_);
if (v_isRec_440_ == 0)
{
lean_del_object(v___x_438_);
goto v___jp_431_;
}
else
{
if (v_eager_422_ == 0)
{
lean_del_object(v___x_438_);
goto v___jp_431_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_443_; 
lean_del_object(v___x_429_);
lean_dec(v_declName_421_);
v___x_441_ = lean_box(0);
if (v_isShared_439_ == 0)
{
lean_ctor_set_tag(v___x_438_, 0);
lean_ctor_set(v___x_438_, 0, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_del_object(v___x_429_);
lean_dec(v_a_427_);
lean_dec(v_declName_421_);
v___x_446_ = lean_box(0);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
v___jp_431_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v_declName_421_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f___boxed(lean_object* v_declName_449_, lean_object* v_eager_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
uint8_t v_eager_boxed_454_; lean_object* v_res_455_; 
v_eager_boxed_454_ = lean_unbox(v_eager_450_);
v_res_455_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_449_, v_eager_boxed_454_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object* v_declName_456_, uint8_t v_eager_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_456_, v_eager_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_476_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_476_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
if (lean_obj_tag(v_a_462_) == 0)
{
uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = 0;
v___x_467_ = lean_box(v___x_466_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
else
{
uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec_ref_known(v_a_462_, 1);
v___x_471_ = 1;
v___x_472_ = lean_box(v___x_471_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_472_);
v___x_474_ = v___x_464_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_461_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_461_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate___boxed(lean_object* v_declName_485_, lean_object* v_eager_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
uint8_t v_eager_boxed_490_; lean_object* v_res_491_; 
v_eager_boxed_490_ = lean_unbox(v_eager_486_);
v_res_491_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_485_, v_eager_boxed_490_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object* v_declName_492_, uint8_t v_eager_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_492_, v_eager_493_, v_a_496_, v_a_497_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_510_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_510_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
if (lean_obj_tag(v_a_500_) == 1)
{
lean_object* v_val_504_; lean_object* v___x_505_; 
lean_del_object(v___x_502_);
v_val_504_ = lean_ctor_get(v_a_500_, 0);
lean_inc(v_val_504_);
lean_dec_ref_known(v_a_500_, 1);
v___x_505_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_504_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_508_; 
lean_dec(v_a_500_);
v___x_506_ = lean_box(0);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_506_);
v___x_508_ = v___x_502_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_499_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_499_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f___boxed(lean_object* v_declName_519_, lean_object* v_eager_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
uint8_t v_eager_boxed_526_; lean_object* v_res_527_; 
v_eager_boxed_526_ = lean_unbox(v_eager_520_);
v_res_527_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_519_, v_eager_boxed_526_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
return v_res_527_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_528_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_531_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_532_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
lean_ctor_set(v___x_534_, 2, v___x_533_);
lean_ctor_set(v___x_534_, 3, v___x_533_);
lean_ctor_set(v___x_534_, 4, v___x_532_);
lean_ctor_set(v___x_534_, 5, v___x_532_);
lean_ctor_set(v___x_534_, 6, v___x_532_);
lean_ctor_set(v___x_534_, 7, v___x_532_);
lean_ctor_set(v___x_534_, 8, v___x_532_);
lean_ctor_set(v___x_534_, 9, v___x_532_);
lean_ctor_set(v___x_534_, 10, v___x_531_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_unsigned_to_nat(32u);
v___x_536_ = lean_mk_empty_array_with_capacity(v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_538_ = ((size_t)5ULL);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_unsigned_to_nat(32u);
v___x_541_ = lean_mk_empty_array_with_capacity(v___x_540_);
v___x_542_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3);
v___x_543_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___x_541_);
lean_ctor_set(v___x_543_, 2, v___x_539_);
lean_ctor_set(v___x_543_, 3, v___x_539_);
lean_ctor_set_usize(v___x_543_, 4, v___x_538_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_544_ = lean_box(1);
v___x_545_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4);
v___x_546_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1);
v___x_547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_545_);
lean_ctor_set(v___x_547_, 2, v___x_544_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(lean_object* v_msgData_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; lean_object* v_toCold_553_; lean_object* v_env_554_; lean_object* v_options_555_; uint8_t v___x_556_; lean_object* v_env_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_552_ = lean_st_ref_get(v___y_550_);
v_toCold_553_ = lean_ctor_get(v___y_549_, 0);
v_env_554_ = lean_ctor_get(v___x_552_, 0);
lean_inc_ref(v_env_554_);
lean_dec(v___x_552_);
v_options_555_ = lean_ctor_get(v_toCold_553_, 2);
v___x_556_ = 0;
v_env_557_ = l_Lean_Environment_setRecordingDeps(v_env_554_, v___x_556_);
v___x_558_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2);
v___x_559_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_555_);
v___x_560_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_560_, 0, v_env_557_);
lean_ctor_set(v___x_560_, 1, v___x_558_);
lean_ctor_set(v___x_560_, 2, v___x_559_);
lean_ctor_set(v___x_560_, 3, v_options_555_);
v___x_561_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v_msgData_548_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___boxed(lean_object* v_msgData_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msgData_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_ref_572_; lean_object* v___x_573_; lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_582_; 
v_ref_572_ = lean_ctor_get(v___y_569_, 2);
v___x_573_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msg_568_, v___y_569_, v___y_570_);
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_582_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
lean_inc(v_ref_572_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_ref_572_);
lean_ctor_set(v___x_578_, 1, v_a_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 1);
lean_ctor_set(v___x_576_, 0, v___x_578_);
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg___boxed(lean_object* v_msg_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v_msg_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_587_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__1(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__0));
v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__3(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__2));
v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__5(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__4));
v___x_596_ = l_Lean_stringToMessageData(v___x_595_);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__7(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__6));
v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object* v_declName_600_, uint8_t v_eager_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___x_605_; 
lean_inc(v_declName_600_);
v___x_605_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_600_, v_eager_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_628_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_628_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_628_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_628_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
uint8_t v___x_610_; 
v___x_610_ = lean_unbox(v_a_606_);
if (v___x_610_ == 0)
{
lean_del_object(v___x_608_);
if (v_eager_601_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v_a_606_);
v___x_611_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__1, &l_Lean_Meta_Grind_validateCasesAttr___closed__1_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__1);
v___x_612_ = l_Lean_MessageData_ofConstName(v_declName_600_, v_eager_601_);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__3, &l_Lean_Meta_Grind_validateCasesAttr___closed__3_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__3);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_615_, v_a_602_, v_a_603_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_617_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__5, &l_Lean_Meta_Grind_validateCasesAttr___closed__5_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__5);
v___x_618_ = lean_unbox(v_a_606_);
lean_dec(v_a_606_);
v___x_619_ = l_Lean_MessageData_ofConstName(v_declName_600_, v___x_618_);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_617_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__7, &l_Lean_Meta_Grind_validateCasesAttr___closed__7_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__7);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_622_, v_a_602_, v_a_603_);
return v___x_623_;
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_626_; 
lean_dec(v_a_606_);
lean_dec(v_declName_600_);
v___x_624_ = lean_box(0);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_624_);
v___x_626_ = v___x_608_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_declName_600_);
v_a_629_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_605_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_605_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr___boxed(lean_object* v_declName_637_, lean_object* v_eager_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
uint8_t v_eager_boxed_642_; lean_object* v_res_643_; 
v_eager_boxed_642_ = lean_unbox(v_eager_638_);
v_res_643_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_637_, v_eager_boxed_642_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(lean_object* v_00_u03b1_644_, lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v_msg_645_, v___y_646_, v___y_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_650_, lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(v_00_u03b1_650_, v_msg_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object* v_s_656_, lean_object* v_declName_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_s_656_, v_declName_657_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v_s_656_);
v___x_662_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_657_, v_a_658_, v_a_659_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_s_656_, v_declName_657_);
lean_dec(v_declName_657_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl___boxed(lean_object* v_s_665_, lean_object* v_declName_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_s_665_, v_declName_666_, v_a_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
return v_res_670_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0));
v___x_673_ = l_Lean_stringToMessageData(v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2));
v___x_676_ = l_Lean_stringToMessageData(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object* v_declName_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
uint8_t v___x_681_; 
v___x_681_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_677_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_declName_677_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_684_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1);
v___x_685_ = 0;
v___x_686_ = l_Lean_MessageData_ofConstName(v_declName_677_, v___x_685_);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_684_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_689_, v_a_678_, v_a_679_);
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___boxed(lean_object* v_declName_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_691_, v_a_692_, v_a_693_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
if (lean_obj_tag(v_e_696_) == 1)
{
lean_object* v_fvarId_702_; lean_object* v___x_703_; 
v_fvarId_702_ = lean_ctor_get(v_e_696_, 0);
lean_inc(v_fvarId_702_);
lean_dec_ref_known(v_e_696_, 1);
v___x_703_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_702_, v_a_697_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_720_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_720_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_720_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_720_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_lctx_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v_lctx_708_ = lean_ctor_get(v_a_697_, 2);
v___x_709_ = l_Lean_LocalDecl_index(v_a_704_);
lean_inc_ref(v_lctx_708_);
v___x_710_ = lean_local_ctx_num_indices(v_lctx_708_);
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = lean_nat_sub(v___x_710_, v___x_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_nat_dec_eq(v___x_709_, v___x_712_);
lean_dec(v___x_712_);
lean_dec(v___x_709_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_del_object(v___x_706_);
v___x_714_ = l_Lean_LocalDecl_type(v_a_704_);
lean_dec(v_a_704_);
v___x_715_ = l_Lean_Meta_isProp(v___x_714_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_718_; 
lean_dec(v_a_704_);
v___x_716_ = lean_box(v___x_713_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_716_);
v___x_718_ = v___x_706_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
v_a_721_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_703_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_703_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref(v_e_696_);
v___x_729_ = 0;
v___x_730_ = lean_box(v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar___boxed(lean_object* v_e_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
return v_res_738_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3));
v___x_746_ = l_Lean_stringToMessageData(v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(lean_object* v_mvarId_747_, lean_object* v_e_748_, lean_object* v_type_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
v___x_756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4);
v___x_757_ = l_Lean_MessageData_ofExpr(v_e_748_);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Lean_indentExpr(v_type_749_);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
v___x_762_ = l_Lean_Meta_throwTacticEx___redArg(v___x_755_, v_mvarId_747_, v___x_761_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___boxed(lean_object* v_mvarId_763_, lean_object* v_e_764_, lean_object* v_type_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_763_, v_e_764_, v_type_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(lean_object* v_mvarId_772_, lean_object* v_e_773_, lean_object* v_00_u03b1_774_, lean_object* v_type_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_772_, v_e_773_, v_type_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___boxed(lean_object* v_mvarId_782_, lean_object* v_e_783_, lean_object* v_00_u03b1_784_, lean_object* v_type_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(v_mvarId_782_, v_e_783_, v_00_u03b1_784_, v_type_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(lean_object* v_mvarId_792_, lean_object* v_x_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_792_, v_x_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_a_808_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_799_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_799_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg___boxed(lean_object* v_mvarId_816_, lean_object* v_x_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_816_, v_x_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(lean_object* v_00_u03b1_824_, lean_object* v_mvarId_825_, lean_object* v_x_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_825_, v_x_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___boxed(lean_object* v_00_u03b1_833_, lean_object* v_mvarId_834_, lean_object* v_x_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(v_00_u03b1_833_, v_mvarId_834_, v_x_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(lean_object* v_as_842_, size_t v_i_843_, size_t v_stop_844_, lean_object* v_b_845_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = lean_usize_dec_eq(v_i_843_, v_stop_844_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; size_t v___x_850_; size_t v___x_851_; 
v___x_847_ = 1;
v___x_848_ = lean_array_uget_borrowed(v_as_842_, v_i_843_);
lean_inc(v___x_848_);
v___x_849_ = l_Lean_LocalContext_setKind(v_b_845_, v___x_848_, v___x_847_);
v___x_850_ = ((size_t)1ULL);
v___x_851_ = lean_usize_add(v_i_843_, v___x_850_);
v_i_843_ = v___x_851_;
v_b_845_ = v___x_849_;
goto _start;
}
else
{
return v_b_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4___boxed(lean_object* v_as_853_, lean_object* v_i_854_, lean_object* v_stop_855_, lean_object* v_b_856_){
_start:
{
size_t v_i_boxed_857_; size_t v_stop_boxed_858_; lean_object* v_res_859_; 
v_i_boxed_857_ = lean_unbox_usize(v_i_854_);
lean_dec(v_i_854_);
v_stop_boxed_858_ = lean_unbox_usize(v_stop_855_);
lean_dec(v_stop_855_);
v_res_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_as_853_, v_i_boxed_857_, v_stop_boxed_858_, v_b_856_);
lean_dec_ref(v_as_853_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_ks_864_; lean_object* v_vs_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_889_; 
v_ks_864_ = lean_ctor_get(v_x_860_, 0);
v_vs_865_ = lean_ctor_get(v_x_860_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_x_860_);
if (v_isSharedCheck_889_ == 0)
{
v___x_867_ = v_x_860_;
v_isShared_868_ = v_isSharedCheck_889_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_vs_865_);
lean_inc(v_ks_864_);
lean_dec(v_x_860_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_889_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = lean_array_get_size(v_ks_864_);
v___x_870_ = lean_nat_dec_lt(v_x_861_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_dec(v_x_861_);
v___x_871_ = lean_array_push(v_ks_864_, v_x_862_);
v___x_872_ = lean_array_push(v_vs_865_, v_x_863_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_872_);
lean_ctor_set(v___x_867_, 0, v___x_871_);
v___x_874_ = v___x_867_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
else
{
lean_object* v_k_x27_876_; uint8_t v___x_877_; 
v_k_x27_876_ = lean_array_fget_borrowed(v_ks_864_, v_x_861_);
v___x_877_ = l_Lean_instBEqMVarId_beq(v_x_862_, v_k_x27_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_879_; 
if (v_isShared_868_ == 0)
{
v___x_879_ = v___x_867_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_ks_864_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_vs_865_);
v___x_879_ = v_reuseFailAlloc_883_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = lean_nat_add(v_x_861_, v___x_880_);
lean_dec(v_x_861_);
v_x_860_ = v___x_879_;
v_x_861_ = v___x_881_;
goto _start;
}
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_884_ = lean_array_fset(v_ks_864_, v_x_861_, v_x_862_);
v___x_885_ = lean_array_fset(v_vs_865_, v_x_861_, v_x_863_);
lean_dec(v_x_861_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_885_);
lean_ctor_set(v___x_867_, 0, v___x_884_);
v___x_887_ = v___x_867_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(lean_object* v_n_890_, lean_object* v_k_891_, lean_object* v_v_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(v_n_890_, v___x_893_, v_k_891_, v_v_892_);
return v___x_894_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(lean_object* v_x_896_, size_t v_x_897_, size_t v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
if (lean_obj_tag(v_x_896_) == 0)
{
lean_object* v_es_901_; size_t v___x_902_; size_t v___x_903_; lean_object* v_j_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_es_901_ = lean_ctor_get(v_x_896_, 0);
v___x_902_ = ((size_t)31ULL);
v___x_903_ = lean_usize_land(v_x_897_, v___x_902_);
v_j_904_ = lean_usize_to_nat(v___x_903_);
v___x_905_ = lean_array_get_size(v_es_901_);
v___x_906_ = lean_nat_dec_lt(v_j_904_, v___x_905_);
if (v___x_906_ == 0)
{
lean_dec(v_j_904_);
lean_dec(v_x_900_);
lean_dec(v_x_899_);
return v_x_896_;
}
else
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_945_; 
lean_inc_ref(v_es_901_);
v_isSharedCheck_945_ = !lean_is_exclusive(v_x_896_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v_x_896_, 0);
lean_dec(v_unused_946_);
v___x_908_ = v_x_896_;
v_isShared_909_ = v_isSharedCheck_945_;
goto v_resetjp_907_;
}
else
{
lean_dec(v_x_896_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_945_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_v_910_; lean_object* v___x_911_; lean_object* v_xs_x27_912_; lean_object* v___y_914_; 
v_v_910_ = lean_array_fget(v_es_901_, v_j_904_);
v___x_911_ = lean_box(0);
v_xs_x27_912_ = lean_array_fset(v_es_901_, v_j_904_, v___x_911_);
switch(lean_obj_tag(v_v_910_))
{
case 0:
{
lean_object* v_key_919_; lean_object* v_val_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_930_; 
v_key_919_ = lean_ctor_get(v_v_910_, 0);
v_val_920_ = lean_ctor_get(v_v_910_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v_v_910_);
if (v_isSharedCheck_930_ == 0)
{
v___x_922_ = v_v_910_;
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_val_920_);
lean_inc(v_key_919_);
lean_dec(v_v_910_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
uint8_t v___x_924_; 
v___x_924_ = l_Lean_instBEqMVarId_beq(v_x_899_, v_key_919_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_del_object(v___x_922_);
v___x_925_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_919_, v_val_920_, v_x_899_, v_x_900_);
v___x_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
v___y_914_ = v___x_926_;
goto v___jp_913_;
}
else
{
lean_object* v___x_928_; 
lean_dec(v_val_920_);
lean_dec(v_key_919_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v_x_900_);
lean_ctor_set(v___x_922_, 0, v_x_899_);
v___x_928_ = v___x_922_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_x_899_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_x_900_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
v___y_914_ = v___x_928_;
goto v___jp_913_;
}
}
}
}
case 1:
{
lean_object* v_node_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_943_; 
v_node_931_ = lean_ctor_get(v_v_910_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v_v_910_);
if (v_isSharedCheck_943_ == 0)
{
v___x_933_ = v_v_910_;
v_isShared_934_ = v_isSharedCheck_943_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_node_931_);
lean_dec(v_v_910_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_943_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
size_t v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_935_ = ((size_t)5ULL);
v___x_936_ = lean_usize_shift_right(v_x_897_, v___x_935_);
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_add(v_x_898_, v___x_937_);
v___x_939_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_node_931_, v___x_936_, v___x_938_, v_x_899_, v_x_900_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_939_);
v___x_941_ = v___x_933_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
v___y_914_ = v___x_941_;
goto v___jp_913_;
}
}
}
default: 
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_x_899_);
lean_ctor_set(v___x_944_, 1, v_x_900_);
v___y_914_ = v___x_944_;
goto v___jp_913_;
}
}
v___jp_913_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_array_fset(v_xs_x27_912_, v_j_904_, v___y_914_);
lean_dec(v_j_904_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_915_);
v___x_917_ = v___x_908_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
else
{
lean_object* v_ks_947_; lean_object* v_vs_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_966_; 
v_ks_947_ = lean_ctor_get(v_x_896_, 0);
v_vs_948_ = lean_ctor_get(v_x_896_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_x_896_);
if (v_isSharedCheck_966_ == 0)
{
v___x_950_ = v_x_896_;
v_isShared_951_ = v_isSharedCheck_966_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_vs_948_);
lean_inc(v_ks_947_);
lean_dec(v_x_896_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_966_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_ks_947_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_vs_948_);
v___x_953_ = v_reuseFailAlloc_965_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v_newNode_954_; size_t v___x_955_; uint8_t v___x_956_; 
v_newNode_954_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(v___x_953_, v_x_899_, v_x_900_);
v___x_955_ = ((size_t)7ULL);
v___x_956_ = lean_usize_dec_le(v___x_955_, v_x_898_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_957_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_954_);
v___x_958_ = lean_unsigned_to_nat(4u);
v___x_959_ = lean_nat_dec_lt(v___x_957_, v___x_958_);
lean_dec(v___x_957_);
if (v___x_959_ == 0)
{
lean_object* v_ks_960_; lean_object* v_vs_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_ks_960_ = lean_ctor_get(v_newNode_954_, 0);
lean_inc_ref(v_ks_960_);
v_vs_961_ = lean_ctor_get(v_newNode_954_, 1);
lean_inc_ref(v_vs_961_);
lean_dec_ref(v_newNode_954_);
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_964_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_x_898_, v_ks_960_, v_vs_961_, v___x_962_, v___x_963_);
lean_dec_ref(v_vs_961_);
lean_dec_ref(v_ks_960_);
return v___x_964_;
}
else
{
return v_newNode_954_;
}
}
else
{
return v_newNode_954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(size_t v_depth_967_, lean_object* v_keys_968_, lean_object* v_vals_969_, lean_object* v_i_970_, lean_object* v_entries_971_){
_start:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_array_get_size(v_keys_968_);
v___x_973_ = lean_nat_dec_lt(v_i_970_, v___x_972_);
if (v___x_973_ == 0)
{
lean_dec(v_i_970_);
return v_entries_971_;
}
else
{
lean_object* v_k_974_; lean_object* v_v_975_; uint64_t v___x_976_; size_t v_h_977_; size_t v___x_978_; lean_object* v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; size_t v_h_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_k_974_ = lean_array_fget_borrowed(v_keys_968_, v_i_970_);
v_v_975_ = lean_array_fget_borrowed(v_vals_969_, v_i_970_);
v___x_976_ = l_Lean_instHashableMVarId_hash(v_k_974_);
v_h_977_ = lean_uint64_to_usize(v___x_976_);
v___x_978_ = ((size_t)5ULL);
v___x_979_ = lean_unsigned_to_nat(1u);
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_sub(v_depth_967_, v___x_980_);
v___x_982_ = lean_usize_mul(v___x_978_, v___x_981_);
v_h_983_ = lean_usize_shift_right(v_h_977_, v___x_982_);
v___x_984_ = lean_nat_add(v_i_970_, v___x_979_);
lean_dec(v_i_970_);
lean_inc(v_v_975_);
lean_inc(v_k_974_);
v___x_985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_entries_971_, v_h_983_, v_depth_967_, v_k_974_, v_v_975_);
v_i_970_ = v___x_984_;
v_entries_971_ = v___x_985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg___boxed(lean_object* v_depth_987_, lean_object* v_keys_988_, lean_object* v_vals_989_, lean_object* v_i_990_, lean_object* v_entries_991_){
_start:
{
size_t v_depth_boxed_992_; lean_object* v_res_993_; 
v_depth_boxed_992_ = lean_unbox_usize(v_depth_987_);
lean_dec(v_depth_987_);
v_res_993_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_boxed_992_, v_keys_988_, v_vals_989_, v_i_990_, v_entries_991_);
lean_dec_ref(v_vals_989_);
lean_dec_ref(v_keys_988_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_, lean_object* v_x_998_){
_start:
{
size_t v_x_11773__boxed_999_; size_t v_x_11774__boxed_1000_; lean_object* v_res_1001_; 
v_x_11773__boxed_999_ = lean_unbox_usize(v_x_995_);
lean_dec(v_x_995_);
v_x_11774__boxed_1000_ = lean_unbox_usize(v_x_996_);
lean_dec(v_x_996_);
v_res_1001_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_994_, v_x_11773__boxed_999_, v_x_11774__boxed_1000_, v_x_997_, v_x_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
uint64_t v___x_1005_; size_t v___x_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
v___x_1005_ = l_Lean_instHashableMVarId_hash(v_x_1003_);
v___x_1006_ = lean_uint64_to_usize(v___x_1005_);
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_1002_, v___x_1006_, v___x_1007_, v_x_1003_, v_x_1004_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(lean_object* v_mvarId_1009_, lean_object* v_val_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; lean_object* v_mctx_1014_; lean_object* v_cache_1015_; lean_object* v_zetaDeltaFVarIds_1016_; lean_object* v_postponed_1017_; lean_object* v_diag_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1047_; 
v___x_1013_ = lean_st_ref_take(v___y_1011_);
v_mctx_1014_ = lean_ctor_get(v___x_1013_, 0);
v_cache_1015_ = lean_ctor_get(v___x_1013_, 1);
v_zetaDeltaFVarIds_1016_ = lean_ctor_get(v___x_1013_, 2);
v_postponed_1017_ = lean_ctor_get(v___x_1013_, 3);
v_diag_1018_ = lean_ctor_get(v___x_1013_, 4);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1020_ = v___x_1013_;
v_isShared_1021_ = v_isSharedCheck_1047_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_diag_1018_);
lean_inc(v_postponed_1017_);
lean_inc(v_zetaDeltaFVarIds_1016_);
lean_inc(v_cache_1015_);
lean_inc(v_mctx_1014_);
lean_dec(v___x_1013_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1047_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v_depth_1022_; lean_object* v_levelAssignDepth_1023_; lean_object* v_lmvarCounter_1024_; lean_object* v_mvarCounter_1025_; lean_object* v_lDecls_1026_; lean_object* v_decls_1027_; lean_object* v_userNames_1028_; lean_object* v_lAssignment_1029_; lean_object* v_eAssignment_1030_; lean_object* v_dAssignment_1031_; lean_object* v_synthNormMemo_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1046_; 
v_depth_1022_ = lean_ctor_get(v_mctx_1014_, 0);
v_levelAssignDepth_1023_ = lean_ctor_get(v_mctx_1014_, 1);
v_lmvarCounter_1024_ = lean_ctor_get(v_mctx_1014_, 2);
v_mvarCounter_1025_ = lean_ctor_get(v_mctx_1014_, 3);
v_lDecls_1026_ = lean_ctor_get(v_mctx_1014_, 4);
v_decls_1027_ = lean_ctor_get(v_mctx_1014_, 5);
v_userNames_1028_ = lean_ctor_get(v_mctx_1014_, 6);
v_lAssignment_1029_ = lean_ctor_get(v_mctx_1014_, 7);
v_eAssignment_1030_ = lean_ctor_get(v_mctx_1014_, 8);
v_dAssignment_1031_ = lean_ctor_get(v_mctx_1014_, 9);
v_synthNormMemo_1032_ = lean_ctor_get(v_mctx_1014_, 10);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_mctx_1014_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1034_ = v_mctx_1014_;
v_isShared_1035_ = v_isSharedCheck_1046_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_synthNormMemo_1032_);
lean_inc(v_dAssignment_1031_);
lean_inc(v_eAssignment_1030_);
lean_inc(v_lAssignment_1029_);
lean_inc(v_userNames_1028_);
lean_inc(v_decls_1027_);
lean_inc(v_lDecls_1026_);
lean_inc(v_mvarCounter_1025_);
lean_inc(v_lmvarCounter_1024_);
lean_inc(v_levelAssignDepth_1023_);
lean_inc(v_depth_1022_);
lean_dec(v_mctx_1014_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1046_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1036_ = lean_box(0);
v___x_1037_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(v_eAssignment_1030_, v_mvarId_1009_, v_val_1010_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 8, v___x_1037_);
v___x_1039_ = v___x_1034_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_depth_1022_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_levelAssignDepth_1023_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_lmvarCounter_1024_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_mvarCounter_1025_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_lDecls_1026_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v_decls_1027_);
lean_ctor_set(v_reuseFailAlloc_1045_, 6, v_userNames_1028_);
lean_ctor_set(v_reuseFailAlloc_1045_, 7, v_lAssignment_1029_);
lean_ctor_set(v_reuseFailAlloc_1045_, 8, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1045_, 9, v_dAssignment_1031_);
lean_ctor_set(v_reuseFailAlloc_1045_, 10, v_synthNormMemo_1032_);
v___x_1039_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1039_);
v___x_1041_ = v___x_1020_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_cache_1015_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v_zetaDeltaFVarIds_1016_);
lean_ctor_set(v_reuseFailAlloc_1044_, 3, v_postponed_1017_);
lean_ctor_set(v_reuseFailAlloc_1044_, 4, v_diag_1018_);
v___x_1041_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_st_ref_put(v___y_1011_, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1036_);
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg___boxed(lean_object* v_mvarId_1048_, lean_object* v_val_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1048_, v_val_1049_, v___y_1050_);
lean_dec(v___y_1050_);
return v_res_1052_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1));
v___x_1057_ = l_Lean_MessageData_ofFormat(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(lean_object* v_upperBound_1060_, lean_object* v___y_1061_, lean_object* v___x_1062_, lean_object* v___x_1063_, lean_object* v_a_1064_, lean_object* v_mvarId_1065_, lean_object* v_a_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_nat_dec_lt(v_a_1066_, v_upperBound_1060_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
lean_dec(v_a_1066_);
lean_dec(v_mvarId_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___y_1061_);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_b_1067_);
return v___x_1074_;
}
else
{
lean_object* v_snd_1075_; lean_object* v_snd_1076_; lean_object* v_fst_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1159_; 
v_snd_1075_ = lean_ctor_get(v_b_1067_, 1);
lean_inc(v_snd_1075_);
v_snd_1076_ = lean_ctor_get(v_snd_1075_, 1);
lean_inc(v_snd_1076_);
v_fst_1077_ = lean_ctor_get(v_b_1067_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_b_1067_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v_b_1067_, 1);
lean_dec(v_unused_1160_);
v___x_1079_ = v_b_1067_;
v_isShared_1080_ = v_isSharedCheck_1159_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_fst_1077_);
lean_dec(v_b_1067_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1159_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_fst_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1157_; 
v_fst_1081_ = lean_ctor_get(v_snd_1075_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_snd_1075_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v_snd_1075_, 1);
lean_dec(v_unused_1158_);
v___x_1083_ = v_snd_1075_;
v_isShared_1084_ = v_isSharedCheck_1157_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_fst_1081_);
lean_dec(v_snd_1075_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1157_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_fst_1085_; lean_object* v_snd_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1156_; 
v_fst_1085_ = lean_ctor_get(v_snd_1076_, 0);
v_snd_1086_ = lean_ctor_get(v_snd_1076_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_snd_1076_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1088_ = v_snd_1076_;
v_isShared_1089_ = v_isSharedCheck_1156_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snd_1086_);
lean_inc(v_fst_1085_);
lean_dec(v_snd_1076_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1156_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v_a_1093_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc(v_fst_1081_);
v___x_1097_ = lean_whnf(v_fst_1081_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
if (lean_obj_tag(v_a_1098_) == 7)
{
lean_object* v_binderType_1099_; lean_object* v_body_1100_; lean_object* v___y_1102_; uint8_t v___x_1127_; 
lean_dec(v_fst_1081_);
v_binderType_1099_ = lean_ctor_get(v_a_1098_, 1);
lean_inc_ref(v_binderType_1099_);
v_body_1100_ = lean_ctor_get(v_a_1098_, 2);
lean_inc_ref(v_body_1100_);
lean_dec_ref_known(v_a_1098_, 3);
v___x_1127_ = lean_nat_dec_lt(v___x_1091_, v___x_1063_);
if (v___x_1127_ == 0)
{
lean_inc(v_a_1064_);
v___y_1102_ = v_a_1064_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1128_; 
lean_inc(v_snd_1086_);
lean_inc(v_a_1064_);
v___x_1128_ = l_Lean_Name_num___override(v_a_1064_, v_snd_1086_);
v___y_1102_ = v___x_1128_;
goto v___jp_1101_;
}
v___jp_1101_:
{
uint8_t v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = 2;
lean_inc_ref(v___x_1062_);
lean_inc_ref(v___y_1061_);
v___x_1104_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_1061_, v___x_1062_, v_binderType_1099_, v___x_1103_, v___y_1102_, v___x_1090_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_n(v_a_1105_, 2);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1106_ = l_Lean_Expr_app___override(v_fst_1077_, v_a_1105_);
v___x_1107_ = l_Lean_Expr_mvarId_x21(v_a_1105_);
lean_dec(v_a_1105_);
v___x_1108_ = lean_array_push(v_fst_1085_, v___x_1107_);
v___x_1109_ = lean_nat_add(v_snd_1086_, v___x_1091_);
lean_dec(v_snd_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1109_);
lean_ctor_set(v___x_1088_, 0, v___x_1108_);
v___x_1111_ = v___x_1088_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1111_);
lean_ctor_set(v___x_1083_, 0, v_body_1100_);
v___x_1113_ = v___x_1083_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_body_1100_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v___x_1113_);
lean_ctor_set(v___x_1079_, 0, v___x_1106_);
v___x_1115_ = v___x_1079_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
v_a_1093_ = v___x_1115_;
goto v___jp_1092_;
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v_body_1100_);
lean_del_object(v___x_1088_);
lean_dec(v_snd_1086_);
lean_dec(v_fst_1085_);
lean_del_object(v___x_1083_);
lean_del_object(v___x_1079_);
lean_dec(v_fst_1077_);
lean_dec(v_a_1066_);
lean_dec(v_mvarId_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___y_1061_);
v_a_1119_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1104_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1104_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec(v_a_1098_);
v___x_1129_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3);
lean_inc(v_mvarId_1065_);
v___x_1130_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1096_, v_mvarId_1065_, v___x_1129_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1130_, 1);
if (v_isShared_1089_ == 0)
{
v___x_1132_ = v___x_1088_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_fst_1085_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_snd_1086_);
v___x_1132_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1132_);
v___x_1134_ = v___x_1083_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_fst_1081_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v___x_1134_);
v___x_1136_ = v___x_1079_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_fst_1077_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
v_a_1093_ = v___x_1136_;
goto v___jp_1092_;
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_del_object(v___x_1088_);
lean_dec(v_snd_1086_);
lean_dec(v_fst_1085_);
lean_del_object(v___x_1083_);
lean_dec(v_fst_1081_);
lean_del_object(v___x_1079_);
lean_dec(v_fst_1077_);
lean_dec(v_a_1066_);
lean_dec(v_mvarId_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___y_1061_);
v_a_1140_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1130_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1130_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_del_object(v___x_1088_);
lean_dec(v_snd_1086_);
lean_dec(v_fst_1085_);
lean_del_object(v___x_1083_);
lean_dec(v_fst_1081_);
lean_del_object(v___x_1079_);
lean_dec(v_fst_1077_);
lean_dec(v_a_1066_);
lean_dec(v_mvarId_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___y_1061_);
v_a_1148_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1097_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1097_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
v___jp_1092_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_nat_add(v_a_1066_, v___x_1091_);
lean_dec(v_a_1066_);
v_a_1066_ = v___x_1094_;
v_b_1067_ = v_a_1093_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___boxed(lean_object* v_upperBound_1161_, lean_object* v___y_1162_, lean_object* v___x_1163_, lean_object* v___x_1164_, lean_object* v_a_1165_, lean_object* v_mvarId_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v_upperBound_1161_, v___y_1162_, v___x_1163_, v___x_1164_, v_a_1165_, v_mvarId_1166_, v_a_1167_, v_b_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___x_1164_);
lean_dec(v_upperBound_1161_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(size_t v_sz_1175_, size_t v_i_1176_, lean_object* v_bs_1177_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_lt(v_i_1176_, v_sz_1175_);
if (v___x_1178_ == 0)
{
return v_bs_1177_;
}
else
{
lean_object* v_v_1179_; lean_object* v___x_1180_; lean_object* v_bs_x27_1181_; lean_object* v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; lean_object* v___x_1185_; 
v_v_1179_ = lean_array_uget(v_bs_1177_, v_i_1176_);
v___x_1180_ = lean_unsigned_to_nat(0u);
v_bs_x27_1181_ = lean_array_uset(v_bs_1177_, v_i_1176_, v___x_1180_);
v___x_1182_ = l_Lean_mkFVar(v_v_1179_);
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1176_, v___x_1183_);
v___x_1185_ = lean_array_uset(v_bs_x27_1181_, v_i_1176_, v___x_1182_);
v_i_1176_ = v___x_1184_;
v_bs_1177_ = v___x_1185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2___boxed(lean_object* v_sz_1187_, lean_object* v_i_1188_, lean_object* v_bs_1189_){
_start:
{
size_t v_sz_boxed_1190_; size_t v_i_boxed_1191_; lean_object* v_res_1192_; 
v_sz_boxed_1190_ = lean_unbox_usize(v_sz_1187_);
lean_dec(v_sz_1187_);
v_i_boxed_1191_ = lean_unbox_usize(v_i_1188_);
lean_dec(v_i_1188_);
v_res_1192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_boxed_1190_, v_i_boxed_1191_, v_bs_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0(lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_mvarId_1200_, lean_object* v_fvarId_1201_, lean_object* v_indices_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
size_t v_sz_1208_; size_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_sz_1208_ = lean_array_size(v_indices_1202_);
v___x_1209_ = ((size_t)0ULL);
lean_inc_ref(v_indices_1202_);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_1208_, v___x_1209_, v_indices_1202_);
v___x_1211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
lean_inc_ref(v_a_1198_);
lean_inc(v_fvarId_1201_);
lean_inc(v_mvarId_1200_);
v___x_1212_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_1200_, v___x_1211_, v_fvarId_1201_, v_a_1198_, v___x_1210_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v_lctx_1214_; lean_object* v_localInstances_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___y_1220_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v_lctx_1214_ = lean_ctor_get(v___y_1203_, 2);
v_localInstances_1215_ = lean_ctor_get(v___y_1203_, 3);
v___x_1216_ = 1;
lean_inc(v_fvarId_1201_);
lean_inc_ref(v_lctx_1214_);
v___x_1217_ = l_Lean_LocalContext_setKind(v_lctx_1214_, v_fvarId_1201_, v___x_1216_);
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_array_get_size(v_indices_1202_);
v___x_1263_ = lean_nat_dec_lt(v___x_1218_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_dec_ref(v_indices_1202_);
v___y_1220_ = v___x_1217_;
goto v___jp_1219_;
}
else
{
size_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_usize_of_nat(v___x_1262_);
v___x_1265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_indices_1202_, v___x_1209_, v___x_1264_, v___x_1217_);
lean_dec_ref(v_indices_1202_);
v___y_1220_ = v___x_1265_;
goto v___jp_1219_;
}
v___jp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1221_ = l_Lean_mkAppN(v_a_1213_, v___x_1210_);
lean_dec_ref(v___x_1210_);
v___x_1222_ = l_Lean_mkFVar(v_fvarId_1201_);
v___x_1223_ = l_Lean_Expr_app___override(v___x_1221_, v___x_1222_);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1203_);
lean_inc_ref(v___x_1223_);
v___x_1224_ = lean_infer_type(v___x_1223_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1226_ = l_Lean_Meta_RecursorInfo_numMinors(v_a_1198_);
lean_dec_ref(v_a_1198_);
v___x_1227_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__1));
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_a_1225_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1223_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
lean_inc(v_mvarId_1200_);
lean_inc_ref(v_localInstances_1215_);
v___x_1230_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v___x_1226_, v___y_1220_, v_localInstances_1215_, v___x_1226_, v_a_1199_, v_mvarId_1200_, v___x_1218_, v___x_1229_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___x_1226_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v_snd_1232_; lean_object* v_snd_1233_; lean_object* v_fst_1234_; lean_object* v_fst_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1244_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v_snd_1232_ = lean_ctor_get(v_a_1231_, 1);
v_snd_1233_ = lean_ctor_get(v_snd_1232_, 1);
lean_inc(v_snd_1233_);
v_fst_1234_ = lean_ctor_get(v_a_1231_, 0);
lean_inc(v_fst_1234_);
lean_dec(v_a_1231_);
v_fst_1235_ = lean_ctor_get(v_snd_1233_, 0);
lean_inc(v_fst_1235_);
lean_dec(v_snd_1233_);
v___x_1236_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1200_, v_fst_1234_, v___y_1204_);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v___x_1236_, 0);
lean_dec(v_unused_1245_);
v___x_1238_ = v___x_1236_;
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
else
{
lean_dec(v___x_1236_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = lean_array_to_list(v_fst_1235_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec(v_mvarId_1200_);
v_a_1246_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1230_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1230_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v___x_1223_);
lean_dec_ref(v___y_1220_);
lean_dec(v_mvarId_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
v_a_1254_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1224_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1224_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v___x_1210_);
lean_dec_ref(v_indices_1202_);
lean_dec(v_fvarId_1201_);
lean_dec(v_mvarId_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
v_a_1266_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1212_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1212_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0___boxed(lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_mvarId_1276_, lean_object* v_fvarId_1277_, lean_object* v_indices_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Meta_Grind_cases___lam__0(v_a_1274_, v_a_1275_, v_mvarId_1276_, v_fvarId_1277_, v_indices_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1284_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2));
v___x_1290_ = l_Lean_stringToMessageData(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4));
v___x_1293_ = l_Lean_stringToMessageData(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6));
v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12));
v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_1306_, lean_object* v_declHint_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_env_1312_; uint8_t v___x_1313_; 
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_st_ref_get(v___y_1308_);
v_env_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc_ref(v_env_1312_);
lean_dec(v___x_1311_);
v___x_1313_ = l_Lean_Name_isAnonymous(v_declHint_1307_);
if (v___x_1313_ == 0)
{
uint8_t v_isExporting_1314_; 
v_isExporting_1314_ = lean_ctor_get_uint8(v_env_1312_, sizeof(void*)*13);
if (v_isExporting_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_dec_ref(v_env_1312_);
lean_dec(v_declHint_1307_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_msg_1306_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
lean_inc_ref(v_env_1312_);
v___x_1316_ = l_Lean_Environment_setExporting(v_env_1312_, v___x_1313_);
lean_inc(v_declHint_1307_);
lean_inc_ref(v___x_1316_);
v___x_1317_ = l_Lean_Environment_contains(v___x_1316_, v_declHint_1307_, v_isExporting_1314_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
lean_dec_ref(v___x_1316_);
lean_dec_ref(v_env_1312_);
lean_dec(v_declHint_1307_);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_msg_1306_);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_c_1324_; lean_object* v___x_1325_; 
v___x_1319_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2);
v___x_1320_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5);
v___x_1321_ = l_Lean_Options_empty;
v___x_1322_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1316_);
lean_ctor_set(v___x_1322_, 1, v___x_1319_);
lean_ctor_set(v___x_1322_, 2, v___x_1320_);
lean_ctor_set(v___x_1322_, 3, v___x_1321_);
lean_inc(v_declHint_1307_);
v___x_1323_ = l_Lean_MessageData_ofConstName(v_declHint_1307_, v___x_1313_);
v_c_1324_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1324_, 0, v___x_1322_);
lean_ctor_set(v_c_1324_, 1, v___x_1323_);
v___x_1325_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1312_, v_declHint_1307_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v_env_1312_);
lean_dec(v_declHint_1307_);
v___x_1326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v_c_1324_);
v___x_1328_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = l_Lean_MessageData_note(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_msg_1306_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
else
{
lean_object* v_val_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1367_; 
v_val_1333_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1335_ = v___x_1325_;
v_isShared_1336_ = v_isSharedCheck_1367_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_val_1333_);
lean_dec(v___x_1325_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1367_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v_moduleNames_1338_; lean_object* v_mod_1339_; uint8_t v___x_1340_; 
v___x_1337_ = l_Lean_Environment_header(v_env_1312_);
lean_dec_ref(v_env_1312_);
v_moduleNames_1338_ = lean_ctor_get(v___x_1337_, 4);
lean_inc_ref(v_moduleNames_1338_);
lean_dec_ref(v___x_1337_);
v_mod_1339_ = lean_array_get(v___x_1310_, v_moduleNames_1338_, v_val_1333_);
lean_dec(v_val_1333_);
lean_dec_ref(v_moduleNames_1338_);
v___x_1340_ = l_Lean_isPrivateName(v_declHint_1307_);
lean_dec(v_declHint_1307_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v_c_1324_);
v___x_1343_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = l_Lean_MessageData_ofName(v_mod_1339_);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_MessageData_note(v___x_1348_);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_msg_1306_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1350_);
v___x_1352_ = v___x_1335_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1354_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_c_1324_);
v___x_1356_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_MessageData_ofName(v_mod_1339_);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = l_Lean_MessageData_note(v___x_1361_);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_msg_1306_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1363_);
v___x_1365_ = v___x_1335_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1368_; 
lean_dec_ref(v_env_1312_);
lean_dec(v_declHint_1307_);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v_msg_1306_);
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1369_, lean_object* v_declHint_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1369_, v_declHint_1370_, v___y_1371_);
lean_dec(v___y_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(lean_object* v_msg_1374_, lean_object* v_declHint_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1391_; 
v___x_1381_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1374_, v_declHint_1375_, v___y_1379_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = l_Lean_unknownIdentifierMessageTag;
v___x_1387_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v_a_1382_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1387_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9___boxed(lean_object* v_msg_1392_, lean_object* v_declHint_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_1392_, v_declHint_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(lean_object* v_msgData_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v_env_1407_; uint8_t v___x_1408_; lean_object* v_env_1409_; lean_object* v___x_1410_; lean_object* v_toCold_1411_; lean_object* v_mctx_1412_; lean_object* v_lctx_1413_; lean_object* v_options_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1406_ = lean_st_ref_get(v___y_1404_);
v_env_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_env_1407_);
lean_dec(v___x_1406_);
v___x_1408_ = 0;
v_env_1409_ = l_Lean_Environment_setRecordingDeps(v_env_1407_, v___x_1408_);
v___x_1410_ = lean_st_ref_get(v___y_1402_);
v_toCold_1411_ = lean_ctor_get(v___y_1403_, 0);
v_mctx_1412_ = lean_ctor_get(v___x_1410_, 0);
lean_inc_ref(v_mctx_1412_);
lean_dec(v___x_1410_);
v_lctx_1413_ = lean_ctor_get(v___y_1401_, 2);
v_options_1414_ = lean_ctor_get(v_toCold_1411_, 2);
lean_inc_ref(v_options_1414_);
lean_inc_ref(v_lctx_1413_);
v___x_1415_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1415_, 0, v_env_1409_);
lean_ctor_set(v___x_1415_, 1, v_mctx_1412_);
lean_ctor_set(v___x_1415_, 2, v_lctx_1413_);
lean_ctor_set(v___x_1415_, 3, v_options_1414_);
v___x_1416_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v_msgData_1400_);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16___boxed(lean_object* v_msgData_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msgData_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(lean_object* v_msg_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_ref_1431_; lean_object* v___x_1432_; lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1441_; 
v_ref_1431_ = lean_ctor_get(v___y_1428_, 2);
v___x_1432_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msg_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_inc(v_ref_1431_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_ref_1431_);
lean_ctor_set(v___x_1437_, 1, v_a_1433_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set_tag(v___x_1435_, 1);
lean_ctor_set(v___x_1435_, 0, v___x_1437_);
v___x_1439_ = v___x_1435_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_msg_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(lean_object* v_ref_1449_, lean_object* v_msg_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_toCold_1456_; lean_object* v_currRecDepth_1457_; lean_object* v_ref_1458_; uint16_t v_optionFlags_1459_; uint8_t v_suppressElabErrors_1460_; uint8_t v_isRecordingDeps_1461_; lean_object* v_ref_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_toCold_1456_ = lean_ctor_get(v___y_1453_, 0);
v_currRecDepth_1457_ = lean_ctor_get(v___y_1453_, 1);
v_ref_1458_ = lean_ctor_get(v___y_1453_, 2);
v_optionFlags_1459_ = lean_ctor_get_uint16(v___y_1453_, sizeof(void*)*3);
v_suppressElabErrors_1460_ = lean_ctor_get_uint8(v___y_1453_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1461_ = lean_ctor_get_uint8(v___y_1453_, sizeof(void*)*3 + 3);
v_ref_1462_ = l_Lean_replaceRef(v_ref_1449_, v_ref_1458_);
lean_inc(v_currRecDepth_1457_);
lean_inc_ref(v_toCold_1456_);
v___x_1463_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1463_, 0, v_toCold_1456_);
lean_ctor_set(v___x_1463_, 1, v_currRecDepth_1457_);
lean_ctor_set(v___x_1463_, 2, v_ref_1462_);
lean_ctor_set_uint16(v___x_1463_, sizeof(void*)*3, v_optionFlags_1459_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*3 + 2, v_suppressElabErrors_1460_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*3 + 3, v_isRecordingDeps_1461_);
v___x_1464_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1450_, v___y_1451_, v___y_1452_, v___x_1463_, v___y_1454_);
lean_dec_ref_known(v___x_1463_, 3);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg___boxed(lean_object* v_ref_1465_, lean_object* v_msg_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1465_, v_msg_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v_ref_1465_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_ref_1473_, lean_object* v_msg_1474_, lean_object* v_declHint_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; lean_object* v_a_1482_; lean_object* v___x_1483_; 
v___x_1481_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_1474_, v_declHint_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref(v___x_1481_);
v___x_1483_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1473_, v_a_1482_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1484_, lean_object* v_msg_1485_, lean_object* v_declHint_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1484_, v_msg_1485_, v_declHint_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v_ref_1484_);
return v_res_1492_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1496_, lean_object* v_constName_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1503_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1504_ = 0;
lean_inc(v_constName_1497_);
v___x_1505_ = l_Lean_MessageData_ofConstName(v_constName_1497_, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1503_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1496_, v___x_1508_, v_constName_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1510_, lean_object* v_constName_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1510_, v_constName_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v_ref_1510_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(lean_object* v_constName_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_ref_1524_; lean_object* v___x_1525_; 
v_ref_1524_ = lean_ctor_get(v___y_1521_, 2);
v___x_1525_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1524_, v_constName_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(lean_object* v_constName_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; lean_object* v_env_1540_; uint8_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1539_ = lean_st_ref_get(v___y_1537_);
v_env_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc_ref(v_env_1540_);
lean_dec(v___x_1539_);
v___x_1541_ = 0;
lean_inc(v_constName_1533_);
v___x_1542_ = l_Lean_Environment_find_x3f(v_env_1540_, v_constName_1533_, v___x_1541_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
return v___x_1543_;
}
else
{
lean_object* v_val_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_constName_1533_);
v_val_1544_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1542_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_val_1544_);
lean_dec(v___x_1542_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 0);
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_val_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0___boxed(lean_object* v_constName_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(v_constName_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1(lean_object* v_mvarId_1565_, lean_object* v_e_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; 
lean_inc(v_mvarId_1565_);
v___x_1572_ = l_Lean_MVarId_getTag(v_mvarId_1565_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
lean_inc_ref(v_e_1566_);
v___x_1574_ = lean_infer_type(v_e_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
v___x_1576_ = lean_whnf(v_a_1575_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = l_Lean_Expr_getAppFn(v_a_1577_);
if (lean_obj_tag(v___x_1578_) == 4)
{
lean_object* v_declName_1579_; lean_object* v___x_1580_; 
v_declName_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc_n(v_declName_1579_, 2);
lean_dec_ref_known(v___x_1578_, 2);
v___x_1580_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(v_declName_1579_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
if (lean_obj_tag(v_a_1581_) == 5)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec_ref_known(v_a_1581_, 1);
v___x_1582_ = l_Lean_mkCasesOnName(v_declName_1579_);
v___x_1583_ = lean_box(0);
v___x_1584_ = l_Lean_Meta_mkRecursorInfo(v___x_1582_, v___x_1583_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = l_Lean_Meta_RecursorInfo_numIndices(v_a_1585_);
v___x_1588_ = lean_nat_dec_lt(v___x_1586_, v___x_1587_);
lean_dec(v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; 
lean_inc_ref(v_e_1566_);
v___x_1589_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(v_e_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v_mvarId_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; uint8_t v___x_1613_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1613_ = lean_unbox(v_a_1590_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_inc_ref(v_e_1566_);
v___x_1614_ = l_Lean_Meta_isProof(v_e_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; uint8_t v___x_1616_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = lean_unbox(v_a_1615_);
lean_dec(v_a_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__1));
v___x_1618_ = l_Lean_Core_mkFreshUserName(v___x_1617_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__3));
v___x_1621_ = l_Lean_MVarId_assertExt(v_mvarId_1565_, v_a_1619_, v_a_1577_, v_e_1566_, v___x_1620_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v_mvarId_1592_ = v_a_1622_;
v___y_1593_ = v___y_1567_;
v___y_1594_ = v___y_1568_;
v___y_1595_ = v___y_1569_;
v___y_1596_ = v___y_1570_;
goto v___jp_1591_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1585_);
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
v_a_1623_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1621_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1585_);
lean_dec(v_a_1577_);
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_e_1566_);
lean_dec(v_mvarId_1565_);
v_a_1631_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1618_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1618_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__1));
v___x_1640_ = l_Lean_Core_mkFreshUserName(v___x_1639_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = l_Lean_MVarId_assert(v_mvarId_1565_, v_a_1641_, v_a_1577_, v_e_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1642_, 1);
v_mvarId_1592_ = v_a_1643_;
v___y_1593_ = v___y_1567_;
v___y_1594_ = v___y_1568_;
v___y_1595_ = v___y_1569_;
v___y_1596_ = v___y_1570_;
goto v___jp_1591_;
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1585_);
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
v_a_1644_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1642_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1642_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1585_);
lean_dec(v_a_1577_);
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_e_1566_);
lean_dec(v_mvarId_1565_);
v_a_1652_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1640_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1640_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1585_);
lean_dec(v_a_1577_);
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_e_1566_);
lean_dec(v_mvarId_1565_);
v_a_1660_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1614_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1614_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1577_);
v___x_1668_ = l_Lean_Expr_fvarId_x21(v_e_1566_);
lean_dec_ref(v_e_1566_);
v___x_1669_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__0));
v___x_1670_ = l_Lean_Meta_Grind_cases___lam__0(v_a_1585_, v_a_1573_, v_mvarId_1565_, v___x_1668_, v___x_1669_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v___x_1670_;
}
v___jp_1591_:
{
uint8_t v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_unbox(v_a_1590_);
lean_dec(v_a_1590_);
v___x_1598_ = l_Lean_Meta_intro1Core(v_mvarId_1592_, v___x_1597_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v_fst_1600_; lean_object* v_snd_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v_fst_1600_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_fst_1600_);
v_snd_1601_ = lean_ctor_get(v_a_1599_, 1);
lean_inc_n(v_snd_1601_, 2);
lean_dec(v_a_1599_);
v___x_1602_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__0));
v___x_1603_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__0___boxed), 10, 5);
lean_closure_set(v___x_1603_, 0, v_a_1585_);
lean_closure_set(v___x_1603_, 1, v_a_1573_);
lean_closure_set(v___x_1603_, 2, v_snd_1601_);
lean_closure_set(v___x_1603_, 3, v_fst_1600_);
lean_closure_set(v___x_1603_, 4, v___x_1602_);
v___x_1604_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_snd_1601_, v___x_1603_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
return v___x_1604_;
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v_a_1585_);
lean_dec(v_a_1573_);
v_a_1605_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1598_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1598_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_a_1585_);
lean_dec(v_a_1577_);
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_e_1566_);
lean_dec(v_mvarId_1565_);
v_a_1671_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1589_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1589_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v___x_1679_; 
lean_dec(v_a_1577_);
v___x_1679_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1565_, v_e_1566_, v___x_1583_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v_mvarId_1681_; lean_object* v_indicesFVarIds_1682_; lean_object* v_fvarId_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v_mvarId_1681_ = lean_ctor_get(v_a_1680_, 0);
lean_inc_n(v_mvarId_1681_, 2);
v_indicesFVarIds_1682_ = lean_ctor_get(v_a_1680_, 1);
lean_inc_ref(v_indicesFVarIds_1682_);
v_fvarId_1683_ = lean_ctor_get(v_a_1680_, 2);
lean_inc(v_fvarId_1683_);
lean_dec(v_a_1680_);
v___x_1684_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__0___boxed), 10, 5);
lean_closure_set(v___x_1684_, 0, v_a_1585_);
lean_closure_set(v___x_1684_, 1, v_a_1573_);
lean_closure_set(v___x_1684_, 2, v_mvarId_1681_);
lean_closure_set(v___x_1684_, 3, v_fvarId_1683_);
lean_closure_set(v___x_1684_, 4, v_indicesFVarIds_1682_);
v___x_1685_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_1681_, v___x_1684_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v___x_1685_;
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_a_1585_);
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
v_a_1686_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1679_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1679_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_a_1577_);
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_e_1566_);
lean_dec(v_mvarId_1565_);
v_a_1694_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1584_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1584_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v___x_1702_; 
lean_dec(v_a_1581_);
lean_dec(v_declName_1579_);
lean_dec(v_a_1573_);
v___x_1702_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_1565_, v_e_1566_, v_a_1577_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v___x_1702_;
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_declName_1579_);
lean_dec(v_a_1577_);
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_e_1566_);
lean_dec(v_mvarId_1565_);
v_a_1703_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1580_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1580_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v___x_1711_; 
lean_dec_ref(v___x_1578_);
lean_dec(v_a_1573_);
v___x_1711_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_1565_, v_e_1566_, v_a_1577_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v___x_1711_;
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_e_1566_);
lean_dec(v_mvarId_1565_);
v_a_1712_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1576_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1576_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v_a_1573_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_e_1566_);
lean_dec(v_mvarId_1565_);
v_a_1720_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1574_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1574_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_e_1566_);
lean_dec(v_mvarId_1565_);
v_a_1728_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1572_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1572_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1___boxed(lean_object* v_mvarId_1736_, lean_object* v_e_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_Meta_Grind_cases___lam__1(v_mvarId_1736_, v_e_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases(lean_object* v_mvarId_1744_, lean_object* v_e_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___f_1751_; lean_object* v___x_1752_; 
lean_inc(v_mvarId_1744_);
v___f_1751_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1751_, 0, v_mvarId_1744_);
lean_closure_set(v___f_1751_, 1, v_e_1745_);
v___x_1752_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_1744_, v___f_1751_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___boxed(lean_object* v_mvarId_1753_, lean_object* v_e_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Meta_Grind_cases(v_mvarId_1753_, v_e_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(lean_object* v_mvarId_1761_, lean_object* v_val_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1761_, v_val_1762_, v___y_1764_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___boxed(lean_object* v_mvarId_1769_, lean_object* v_val_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(v_mvarId_1769_, v_val_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(lean_object* v_upperBound_1777_, lean_object* v___y_1778_, lean_object* v___x_1779_, lean_object* v___x_1780_, lean_object* v_a_1781_, lean_object* v_mvarId_1782_, lean_object* v_inst_1783_, lean_object* v_R_1784_, lean_object* v_a_1785_, lean_object* v_b_1786_, lean_object* v_c_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v_upperBound_1777_, v___y_1778_, v___x_1779_, v___x_1780_, v_a_1781_, v_mvarId_1782_, v_a_1785_, v_b_1786_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___boxed(lean_object* v_upperBound_1794_, lean_object* v___y_1795_, lean_object* v___x_1796_, lean_object* v___x_1797_, lean_object* v_a_1798_, lean_object* v_mvarId_1799_, lean_object* v_inst_1800_, lean_object* v_R_1801_, lean_object* v_a_1802_, lean_object* v_b_1803_, lean_object* v_c_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(v_upperBound_1794_, v___y_1795_, v___x_1796_, v___x_1797_, v_a_1798_, v_mvarId_1799_, v_inst_1800_, v_R_1801_, v_a_1802_, v_b_1803_, v_c_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___x_1797_);
lean_dec(v_upperBound_1794_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(lean_object* v_00_u03b1_1811_, lean_object* v_constName_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_constName_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(v_00_u03b1_1819_, v_constName_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2(lean_object* v_00_u03b2_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(v_x_1828_, v_x_1829_, v_x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1832_, lean_object* v_ref_1833_, lean_object* v_constName_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1833_, v_constName_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1841_, lean_object* v_ref_1842_, lean_object* v_constName_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(v_00_u03b1_1841_, v_ref_1842_, v_constName_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v_ref_1842_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1850_, lean_object* v_x_1851_, size_t v_x_1852_, size_t v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_1851_, v_x_1852_, v_x_1853_, v_x_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_){
_start:
{
size_t v_x_13292__boxed_1863_; size_t v_x_13293__boxed_1864_; lean_object* v_res_1865_; 
v_x_13292__boxed_1863_ = lean_unbox_usize(v_x_1859_);
lean_dec(v_x_1859_);
v_x_13293__boxed_1864_ = lean_unbox_usize(v_x_1860_);
lean_dec(v_x_1860_);
v_res_1865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(v_00_u03b2_1857_, v_x_1858_, v_x_13292__boxed_1863_, v_x_13293__boxed_1864_, v_x_1861_, v_x_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b1_1866_, lean_object* v_ref_1867_, lean_object* v_msg_1868_, lean_object* v_declHint_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1867_, v_msg_1868_, v_declHint_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b1_1876_, lean_object* v_ref_1877_, lean_object* v_msg_1878_, lean_object* v_declHint_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(v_00_u03b1_1876_, v_ref_1877_, v_msg_1878_, v_declHint_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v_ref_1877_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_1886_, lean_object* v_n_1887_, lean_object* v_k_1888_, lean_object* v_v_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(v_n_1887_, v_k_1888_, v_v_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(lean_object* v_00_u03b2_1891_, size_t v_depth_1892_, lean_object* v_keys_1893_, lean_object* v_vals_1894_, lean_object* v_heq_1895_, lean_object* v_i_1896_, lean_object* v_entries_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_1892_, v_keys_1893_, v_vals_1894_, v_i_1896_, v_entries_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1899_, lean_object* v_depth_1900_, lean_object* v_keys_1901_, lean_object* v_vals_1902_, lean_object* v_heq_1903_, lean_object* v_i_1904_, lean_object* v_entries_1905_){
_start:
{
size_t v_depth_boxed_1906_; lean_object* v_res_1907_; 
v_depth_boxed_1906_ = lean_unbox_usize(v_depth_1900_);
lean_dec(v_depth_1900_);
v_res_1907_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(v_00_u03b2_1899_, v_depth_boxed_1906_, v_keys_1901_, v_vals_1902_, v_heq_1903_, v_i_1904_, v_entries_1905_);
lean_dec_ref(v_vals_1902_);
lean_dec_ref(v_keys_1901_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(lean_object* v_msg_1908_, lean_object* v_declHint_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1908_, v_declHint_1909_, v___y_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_1916_, lean_object* v_declHint_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(v_msg_1916_, v_declHint_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(lean_object* v_00_u03b1_1924_, lean_object* v_ref_1925_, lean_object* v_msg_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1925_, v_msg_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1933_, lean_object* v_ref_1934_, lean_object* v_msg_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(v_00_u03b1_1933_, v_ref_1934_, v_msg_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v_ref_1934_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13(lean_object* v_00_u03b2_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(v_x_1943_, v_x_1944_, v_x_1945_, v_x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_1948_, lean_object* v_msg_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b1_1956_, lean_object* v_msg_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(v_00_u03b1_1956_, v_msg_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1963_;
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
