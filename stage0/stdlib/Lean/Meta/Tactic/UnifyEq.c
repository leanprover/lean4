// Lean compiler output
// Module: Lean.Meta.Tactic.UnifyEq
// Imports: public import Lean.Meta.Tactic.Injection import Lean.Meta.LitValues import Lean.Meta.StringLitProof import Init.Data.Nat.Internal.Linear import Init.Data.Char.Basic import Init.Data.Int.Basic import Init.Data.SInt.Basic
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Meta_getFinValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lean_Meta_getInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int8_dec_eq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_getInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_Meta_getInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Meta_getInt64Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkStringLitNeProof___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_of_beq_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(152, 213, 144, 137, 140, 238, 73, 24)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ne_of_toNat_beq_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(242, 84, 129, 199, 181, 37, 69, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ne_of_neg_toNat_beq_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(144, 99, 31, 109, 68, 235, 99, 37)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__9_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(105, 132, 165, 49, 57, 212, 177, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__12_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ne_of_val_beq_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(37, 129, 185, 84, 165, 77, 20, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__16_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(23, 116, 193, 2, 245, 244, 80, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__19_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(19, 142, 158, 229, 248, 103, 18, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__22_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(101, 48, 5, 44, 219, 160, 121, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__25_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(153, 160, 209, 250, 44, 43, 85, 193)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__28_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__29_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__30_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(177, 201, 208, 243, 23, 206, 4, 18)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__31_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__33_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(254, 117, 38, 80, 176, 126, 99, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__34_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__34_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__35_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__36_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__36_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__37_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(242, 180, 43, 253, 27, 114, 53, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__37 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__37_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__37_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__39_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__39_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(33, 168, 88, 24, 55, 185, 59, 80)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__40_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__41_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__42_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__42_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__43_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(100, 248, 212, 194, 194, 182, 16, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__43_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__43_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__44_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ofList_ne_ofList"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(7, 129, 74, 87, 236, 194, 167, 197)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(117, 155, 195, 132, 142, 127, 213, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Dependent elimination failed: Failed to solve equation"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nat case `"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_unifyEq_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_unifyEq_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimOffset"};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(94, 91, 22, 141, 221, 120, 153, 253)}};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "succ_ne_zero"};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(87, 138, 114, 183, 27, 252, 104, 142)}};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__5_value;
static const lean_string_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__6_value;
static const lean_string_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(106, 137, 24, 74, 49, 62, 0, 94)}};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_unifyEq_x3f___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_unifyEq_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Expected an equality, but found"};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_unifyEq_x3f___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(lean_object* v_mvarId_1_, lean_object* v_eqDecl_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; lean_object* v___x_11_; 
v___x_8_ = l_Lean_LocalDecl_fvarId(v_eqDecl_2_);
lean_inc(v___x_8_);
v___x_9_ = l_Lean_mkFVar(v___x_8_);
v___x_10_ = 1;
v___x_11_ = l_Lean_Meta_mkEqOfHEq(v___x_9_, v___x_10_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_13_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc_n(v_a_12_, 2);
lean_dec_ref_known(v___x_11_, 1);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_13_ = lean_infer_type(v_a_12_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_13_, 1);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_15_ = lean_whnf(v_a_14_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v___x_15_, 1);
v___x_17_ = l_Lean_LocalDecl_userName(v_eqDecl_2_);
v___x_18_ = l_Lean_MVarId_assert(v_mvarId_1_, v___x_17_, v_a_16_, v_a_12_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_20_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_18_, 1);
v___x_20_ = l_Lean_MVarId_clear(v_a_19_, v___x_8_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
return v___x_20_;
}
else
{
lean_dec(v___x_8_);
return v___x_18_;
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_a_12_);
lean_dec(v___x_8_);
lean_dec(v_mvarId_1_);
v_a_21_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_15_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_15_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
else
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_36_; 
lean_dec(v_a_12_);
lean_dec(v___x_8_);
lean_dec(v_mvarId_1_);
v_a_29_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_36_ == 0)
{
v___x_31_ = v___x_13_;
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_13_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_a_29_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
lean_dec(v___x_8_);
lean_dec(v_mvarId_1_);
v_a_37_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_11_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_11_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27___boxed(lean_object* v_mvarId_45_, lean_object* v_eqDecl_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(v_mvarId_45_, v_eqDecl_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_eqDecl_46_);
return v_res_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = l_Lean_mkNatLit(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(lean_object* v_e_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
lean_inc_ref(v_e_55_);
v___x_61_ = l_Lean_Meta_evalNat(v_e_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_80_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_80_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_80_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_80_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
if (lean_obj_tag(v_a_62_) == 0)
{
lean_object* v___x_66_; 
lean_del_object(v___x_64_);
v___x_66_ = l_Lean_Meta_isOffset_x3f(v_e_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
return v___x_66_;
}
else
{
lean_object* v_val_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_79_; 
lean_dec_ref(v_e_55_);
v_val_67_ = lean_ctor_get(v_a_62_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_a_62_);
if (v_isSharedCheck_79_ == 0)
{
v___x_69_ = v_a_62_;
v_isShared_70_ = v_isSharedCheck_79_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_val_67_);
lean_dec(v_a_62_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_79_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_71_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v_val_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_72_);
v___x_74_ = v___x_69_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_78_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_76_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_74_);
v___x_76_ = v___x_64_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
lean_dec_ref(v_e_55_);
v_a_81_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_61_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_61_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___boxed(lean_object* v_e_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_e_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f(lean_object* v_a_183_, lean_object* v_b_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Meta_getNatValue_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_190_, 1);
if (lean_obj_tag(v_a_191_) == 1)
{
lean_object* v_val_192_; lean_object* v___x_193_; 
lean_dec_ref(v_a_183_);
v_val_192_ = lean_ctor_get(v_a_191_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v_a_191_, 1);
v___x_193_ = l_Lean_Meta_getNatValue_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec_ref(v_b_184_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_212_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_212_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_212_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_212_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
if (lean_obj_tag(v_a_194_) == 1)
{
lean_object* v_val_198_; uint8_t v___x_199_; 
v_val_198_ = lean_ctor_get(v_a_194_, 0);
lean_inc(v_val_198_);
lean_dec_ref_known(v_a_194_, 1);
v___x_199_ = lean_nat_dec_eq(v_val_192_, v_val_198_);
lean_dec(v_val_198_);
lean_dec(v_val_192_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__3));
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_200_);
v___x_202_ = v___x_196_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
else
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = lean_box(0);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_204_);
v___x_206_ = v___x_196_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v___x_208_; lean_object* v___x_210_; 
lean_dec(v_a_194_);
lean_dec(v_val_192_);
v___x_208_ = lean_box(0);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_208_);
v___x_210_ = v___x_196_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_val_192_);
v_a_213_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_193_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_193_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
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
else
{
lean_object* v___x_221_; 
lean_dec(v_a_191_);
lean_inc_ref(v_a_183_);
v___x_221_ = l_Lean_Meta_getIntValue_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref_known(v___x_221_, 1);
if (lean_obj_tag(v_a_222_) == 1)
{
lean_object* v_val_223_; lean_object* v___x_224_; 
lean_dec_ref(v_a_183_);
v_val_223_ = lean_ctor_get(v_a_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v_a_222_, 1);
v___x_224_ = l_Lean_Meta_getIntValue_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_250_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_250_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_250_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_250_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
if (lean_obj_tag(v_a_225_) == 1)
{
lean_object* v_val_229_; uint8_t v___x_230_; 
v_val_229_ = lean_ctor_get(v_a_225_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v_a_225_, 1);
v___x_230_ = lean_int_dec_eq(v_val_223_, v_val_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_231_ = l_Int_toNat(v_val_223_);
lean_dec(v_val_223_);
v___x_232_ = l_Int_toNat(v_val_229_);
lean_dec(v_val_229_);
v___x_233_ = lean_nat_dec_eq(v___x_231_, v___x_232_);
lean_dec(v___x_232_);
lean_dec(v___x_231_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__7));
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_234_);
v___x_236_ = v___x_227_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
else
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__10));
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_238_);
v___x_240_ = v___x_227_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_244_; 
lean_dec(v_val_229_);
lean_dec(v_val_223_);
v___x_242_ = lean_box(0);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_242_);
v___x_244_ = v___x_227_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_248_; 
lean_dec(v_a_225_);
lean_dec(v_val_223_);
v___x_246_ = lean_box(0);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_246_);
v___x_248_ = v___x_227_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec(v_val_223_);
v_a_251_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_224_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_224_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v___x_259_; 
lean_dec(v_a_222_);
lean_inc_ref(v_a_183_);
v___x_259_ = l_Lean_Meta_getCharValue_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
if (lean_obj_tag(v_a_260_) == 1)
{
lean_object* v_val_261_; lean_object* v___x_262_; 
lean_dec_ref(v_a_183_);
v_val_261_ = lean_ctor_get(v_a_260_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v_a_260_, 1);
v___x_262_ = l_Lean_Meta_getCharValue_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_283_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_283_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_283_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_283_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
if (lean_obj_tag(v_a_263_) == 1)
{
lean_object* v_val_267_; uint32_t v___x_268_; uint32_t v___x_269_; uint8_t v___x_270_; 
v_val_267_ = lean_ctor_get(v_a_263_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v_a_263_, 1);
v___x_268_ = lean_unbox_uint32(v_val_261_);
lean_dec(v_val_261_);
v___x_269_ = lean_unbox_uint32(v_val_267_);
lean_dec(v_val_267_);
v___x_270_ = lean_uint32_dec_eq(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__13));
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_271_);
v___x_273_ = v___x_265_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
else
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = lean_box(0);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_275_);
v___x_277_ = v___x_265_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_281_; 
lean_dec(v_a_263_);
lean_dec(v_val_261_);
v___x_279_ = lean_box(0);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_279_);
v___x_281_ = v___x_265_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v_val_261_);
v_a_284_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_262_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_262_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v___x_292_; 
lean_dec(v_a_260_);
lean_inc_ref(v_a_183_);
v___x_292_ = l_Lean_Meta_getFinValue_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_717_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_717_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_717_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_717_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
if (lean_obj_tag(v_a_293_) == 1)
{
lean_object* v_val_297_; lean_object* v_fst_298_; lean_object* v_snd_299_; lean_object* v___x_300_; 
lean_dec_ref(v_a_183_);
v_val_297_ = lean_ctor_get(v_a_293_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v_a_293_, 1);
v_fst_298_ = lean_ctor_get(v_val_297_, 0);
lean_inc(v_fst_298_);
v_snd_299_ = lean_ctor_get(v_val_297_, 1);
lean_inc(v_snd_299_);
lean_dec(v_val_297_);
v___x_300_ = l_Lean_Meta_getFinValue_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_323_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_323_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_323_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_323_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
if (lean_obj_tag(v_a_301_) == 1)
{
lean_object* v_val_310_; lean_object* v_fst_311_; lean_object* v_snd_312_; uint8_t v___x_313_; 
v_val_310_ = lean_ctor_get(v_a_301_, 0);
lean_inc(v_val_310_);
lean_dec_ref_known(v_a_301_, 1);
v_fst_311_ = lean_ctor_get(v_val_310_, 0);
lean_inc(v_fst_311_);
v_snd_312_ = lean_ctor_get(v_val_310_, 1);
lean_inc(v_snd_312_);
lean_dec(v_val_310_);
v___x_313_ = lean_nat_dec_eq(v_fst_298_, v_fst_311_);
lean_dec(v_fst_311_);
lean_dec(v_fst_298_);
if (v___x_313_ == 0)
{
lean_dec(v_snd_312_);
lean_dec(v_snd_299_);
lean_del_object(v___x_295_);
goto v___jp_305_;
}
else
{
uint8_t v___x_314_; 
v___x_314_ = lean_nat_dec_eq(v_snd_299_, v_snd_312_);
lean_dec(v_snd_312_);
lean_dec(v_snd_299_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_317_; 
lean_del_object(v___x_303_);
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__17));
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_315_);
v___x_317_ = v___x_295_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
lean_del_object(v___x_295_);
goto v___jp_305_;
}
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_del_object(v___x_303_);
lean_dec(v_a_301_);
lean_dec(v_snd_299_);
lean_dec(v_fst_298_);
v___x_319_ = lean_box(0);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_319_);
v___x_321_ = v___x_295_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
v___jp_305_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = lean_box(0);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_306_);
v___x_308_ = v___x_303_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_snd_299_);
lean_dec(v_fst_298_);
lean_del_object(v___x_295_);
v_a_324_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_300_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_300_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v___x_332_; 
lean_del_object(v___x_295_);
lean_dec(v_a_293_);
lean_inc_ref(v_a_183_);
v___x_332_ = l_Lean_Meta_getBitVecValue_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_708_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_708_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_708_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_708_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
if (lean_obj_tag(v_a_333_) == 1)
{
lean_object* v_val_337_; lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_340_; 
lean_dec_ref(v_a_183_);
v_val_337_ = lean_ctor_get(v_a_333_, 0);
lean_inc(v_val_337_);
lean_dec_ref_known(v_a_333_, 1);
v_fst_338_ = lean_ctor_get(v_val_337_, 0);
lean_inc(v_fst_338_);
v_snd_339_ = lean_ctor_get(v_val_337_, 1);
lean_inc(v_snd_339_);
lean_dec(v_val_337_);
v___x_340_ = l_Lean_Meta_getBitVecValue_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_363_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_363_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_363_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_363_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
if (lean_obj_tag(v_a_341_) == 1)
{
lean_object* v_val_350_; lean_object* v_fst_351_; lean_object* v_snd_352_; uint8_t v___x_353_; 
v_val_350_ = lean_ctor_get(v_a_341_, 0);
lean_inc(v_val_350_);
lean_dec_ref_known(v_a_341_, 1);
v_fst_351_ = lean_ctor_get(v_val_350_, 0);
lean_inc(v_fst_351_);
v_snd_352_ = lean_ctor_get(v_val_350_, 1);
lean_inc(v_snd_352_);
lean_dec(v_val_350_);
v___x_353_ = lean_nat_dec_eq(v_fst_338_, v_fst_351_);
lean_dec(v_fst_351_);
lean_dec(v_fst_338_);
if (v___x_353_ == 0)
{
lean_dec(v_snd_352_);
lean_dec(v_snd_339_);
lean_del_object(v___x_335_);
goto v___jp_345_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = lean_nat_dec_eq(v_snd_339_, v_snd_352_);
lean_dec(v_snd_352_);
lean_dec(v_snd_339_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_357_; 
lean_del_object(v___x_343_);
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__20));
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_355_);
v___x_357_ = v___x_335_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
else
{
lean_del_object(v___x_335_);
goto v___jp_345_;
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_361_; 
lean_del_object(v___x_343_);
lean_dec(v_a_341_);
lean_dec(v_snd_339_);
lean_dec(v_fst_338_);
v___x_359_ = lean_box(0);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_359_);
v___x_361_ = v___x_335_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
v___jp_345_:
{
lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_346_ = lean_box(0);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_346_);
v___x_348_ = v___x_343_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec(v_snd_339_);
lean_dec(v_fst_338_);
lean_del_object(v___x_335_);
v_a_364_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_340_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_340_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v___x_372_; 
lean_del_object(v___x_335_);
lean_dec(v_a_333_);
lean_inc_ref(v_a_183_);
v___x_372_ = l_Lean_Meta_getUInt8Value_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
if (lean_obj_tag(v_a_373_) == 1)
{
lean_object* v_val_374_; lean_object* v___x_375_; 
lean_dec_ref(v_a_183_);
v_val_374_ = lean_ctor_get(v_a_373_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v_a_373_, 1);
v___x_375_ = l_Lean_Meta_getUInt8Value_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_396_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_396_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_396_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_396_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
if (lean_obj_tag(v_a_376_) == 1)
{
lean_object* v_val_380_; uint8_t v___x_381_; uint8_t v___x_382_; uint8_t v___x_383_; 
v_val_380_ = lean_ctor_get(v_a_376_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v_a_376_, 1);
v___x_381_ = lean_unbox(v_val_374_);
lean_dec(v_val_374_);
v___x_382_ = lean_unbox(v_val_380_);
lean_dec(v_val_380_);
v___x_383_ = lean_uint8_dec_eq(v___x_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__23));
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_384_);
v___x_386_ = v___x_378_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
else
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_box(0);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_388_);
v___x_390_ = v___x_378_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_394_; 
lean_dec(v_a_376_);
lean_dec(v_val_374_);
v___x_392_ = lean_box(0);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_392_);
v___x_394_ = v___x_378_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_val_374_);
v_a_397_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_375_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_375_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v___x_405_; 
lean_dec(v_a_373_);
lean_inc_ref(v_a_183_);
v___x_405_ = l_Lean_Meta_getUInt16Value_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
if (lean_obj_tag(v_a_406_) == 1)
{
lean_object* v_val_407_; lean_object* v___x_408_; 
lean_dec_ref(v_a_183_);
v_val_407_ = lean_ctor_get(v_a_406_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v_a_406_, 1);
v___x_408_ = l_Lean_Meta_getUInt16Value_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_429_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_429_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_429_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_429_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
if (lean_obj_tag(v_a_409_) == 1)
{
lean_object* v_val_413_; uint16_t v___x_414_; uint16_t v___x_415_; uint8_t v___x_416_; 
v_val_413_ = lean_ctor_get(v_a_409_, 0);
lean_inc(v_val_413_);
lean_dec_ref_known(v_a_409_, 1);
v___x_414_ = lean_unbox(v_val_407_);
lean_dec(v_val_407_);
v___x_415_ = lean_unbox(v_val_413_);
lean_dec(v_val_413_);
v___x_416_ = lean_uint16_dec_eq(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__26));
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_417_);
v___x_419_ = v___x_411_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_box(0);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_421_);
v___x_423_ = v___x_411_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_427_; 
lean_dec(v_a_409_);
lean_dec(v_val_407_);
v___x_425_ = lean_box(0);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_425_);
v___x_427_ = v___x_411_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec(v_val_407_);
v_a_430_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_408_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_408_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
lean_object* v___x_438_; 
lean_dec(v_a_406_);
lean_inc_ref(v_a_183_);
v___x_438_ = l_Lean_Meta_getUInt32Value_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
if (lean_obj_tag(v_a_439_) == 1)
{
lean_object* v_val_440_; lean_object* v___x_441_; 
lean_dec_ref(v_a_183_);
v_val_440_ = lean_ctor_get(v_a_439_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_a_439_, 1);
v___x_441_ = l_Lean_Meta_getUInt32Value_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_462_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_462_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_462_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_462_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
if (lean_obj_tag(v_a_442_) == 1)
{
lean_object* v_val_446_; uint32_t v___x_447_; uint32_t v___x_448_; uint8_t v___x_449_; 
v_val_446_ = lean_ctor_get(v_a_442_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v_a_442_, 1);
v___x_447_ = lean_unbox_uint32(v_val_440_);
lean_dec(v_val_440_);
v___x_448_ = lean_unbox_uint32(v_val_446_);
lean_dec(v_val_446_);
v___x_449_ = lean_uint32_dec_eq(v___x_447_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__29));
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_450_);
v___x_452_ = v___x_444_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_box(0);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_454_);
v___x_456_ = v___x_444_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_460_; 
lean_dec(v_a_442_);
lean_dec(v_val_440_);
v___x_458_ = lean_box(0);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_458_);
v___x_460_ = v___x_444_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_val_440_);
v_a_463_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_441_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_441_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v___x_471_; 
lean_dec(v_a_439_);
lean_inc_ref(v_a_183_);
v___x_471_ = l_Lean_Meta_getUInt64Value_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
if (lean_obj_tag(v_a_472_) == 1)
{
lean_object* v_val_473_; lean_object* v___x_474_; 
lean_dec_ref(v_a_183_);
v_val_473_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v_a_472_, 1);
v___x_474_ = l_Lean_Meta_getUInt64Value_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_495_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_495_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_495_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_495_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
if (lean_obj_tag(v_a_475_) == 1)
{
lean_object* v_val_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint8_t v___x_482_; 
v_val_479_ = lean_ctor_get(v_a_475_, 0);
lean_inc(v_val_479_);
lean_dec_ref_known(v_a_475_, 1);
v___x_480_ = lean_unbox_uint64(v_val_473_);
lean_dec(v_val_473_);
v___x_481_ = lean_unbox_uint64(v_val_479_);
lean_dec(v_val_479_);
v___x_482_ = lean_uint64_dec_eq(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__32));
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_483_);
v___x_485_ = v___x_477_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = lean_box(0);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_487_);
v___x_489_ = v___x_477_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_493_; 
lean_dec(v_a_475_);
lean_dec(v_val_473_);
v___x_491_ = lean_box(0);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_491_);
v___x_493_ = v___x_477_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_val_473_);
v_a_496_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_474_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_474_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v___x_504_; 
lean_dec(v_a_472_);
lean_inc_ref(v_a_183_);
v___x_504_ = l_Lean_Meta_getInt8Value_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
if (lean_obj_tag(v_a_505_) == 1)
{
lean_object* v_val_506_; lean_object* v___x_507_; 
lean_dec_ref(v_a_183_);
v_val_506_ = lean_ctor_get(v_a_505_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v_a_505_, 1);
v___x_507_ = l_Lean_Meta_getInt8Value_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_528_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_528_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_528_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_528_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
if (lean_obj_tag(v_a_508_) == 1)
{
lean_object* v_val_512_; uint8_t v___x_513_; uint8_t v___x_514_; uint8_t v___x_515_; 
v_val_512_ = lean_ctor_get(v_a_508_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v_a_508_, 1);
v___x_513_ = lean_unbox(v_val_506_);
lean_dec(v_val_506_);
v___x_514_ = lean_unbox(v_val_512_);
lean_dec(v_val_512_);
v___x_515_ = lean_int8_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__35));
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_516_);
v___x_518_ = v___x_510_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = lean_box(0);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_520_);
v___x_522_ = v___x_510_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_a_508_);
lean_dec(v_val_506_);
v___x_524_ = lean_box(0);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_524_);
v___x_526_ = v___x_510_;
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
lean_dec(v_val_506_);
v_a_529_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_507_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_507_);
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
else
{
lean_object* v___x_537_; 
lean_dec(v_a_505_);
lean_inc_ref(v_a_183_);
v___x_537_ = l_Lean_Meta_getInt16Value_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
if (lean_obj_tag(v_a_538_) == 1)
{
lean_object* v_val_539_; lean_object* v___x_540_; 
lean_dec_ref(v_a_183_);
v_val_539_ = lean_ctor_get(v_a_538_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v_a_538_, 1);
v___x_540_ = l_Lean_Meta_getInt16Value_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_561_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_561_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_561_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_561_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
if (lean_obj_tag(v_a_541_) == 1)
{
lean_object* v_val_545_; uint16_t v___x_546_; uint16_t v___x_547_; uint8_t v___x_548_; 
v_val_545_ = lean_ctor_get(v_a_541_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v_a_541_, 1);
v___x_546_ = lean_unbox(v_val_539_);
lean_dec(v_val_539_);
v___x_547_ = lean_unbox(v_val_545_);
lean_dec(v_val_545_);
v___x_548_ = lean_int16_dec_eq(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__38));
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_549_);
v___x_551_ = v___x_543_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_553_);
v___x_555_ = v___x_543_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec(v_a_541_);
lean_dec(v_val_539_);
v___x_557_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_557_);
v___x_559_ = v___x_543_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_val_539_);
v_a_562_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_540_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_540_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
lean_object* v___x_570_; 
lean_dec(v_a_538_);
lean_inc_ref(v_a_183_);
v___x_570_ = l_Lean_Meta_getInt32Value_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
if (lean_obj_tag(v_a_571_) == 1)
{
lean_object* v_val_572_; lean_object* v___x_573_; 
lean_dec_ref(v_a_183_);
v_val_572_ = lean_ctor_get(v_a_571_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v_a_571_, 1);
v___x_573_ = l_Lean_Meta_getInt32Value_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_594_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_594_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_594_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_594_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
if (lean_obj_tag(v_a_574_) == 1)
{
lean_object* v_val_578_; uint32_t v___x_579_; uint32_t v___x_580_; uint8_t v___x_581_; 
v_val_578_ = lean_ctor_get(v_a_574_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v_a_574_, 1);
v___x_579_ = lean_unbox_uint32(v_val_572_);
lean_dec(v_val_572_);
v___x_580_ = lean_unbox_uint32(v_val_578_);
lean_dec(v_val_578_);
v___x_581_ = lean_int32_dec_eq(v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__41));
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_582_);
v___x_584_ = v___x_576_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = lean_box(0);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_586_);
v___x_588_ = v___x_576_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_592_; 
lean_dec(v_a_574_);
lean_dec(v_val_572_);
v___x_590_ = lean_box(0);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_590_);
v___x_592_ = v___x_576_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_val_572_);
v_a_595_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_573_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_573_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
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
else
{
lean_object* v___x_603_; 
lean_dec(v_a_571_);
v___x_603_ = l_Lean_Meta_getInt64Value_x3f(v_a_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_643_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_643_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_643_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_643_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
if (lean_obj_tag(v_a_604_) == 1)
{
lean_object* v_val_608_; lean_object* v___x_609_; 
lean_del_object(v___x_606_);
v_val_608_ = lean_ctor_get(v_a_604_, 0);
lean_inc(v_val_608_);
lean_dec_ref_known(v_a_604_, 1);
v___x_609_ = l_Lean_Meta_getInt64Value_x3f(v_b_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_630_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_630_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_630_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_630_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
if (lean_obj_tag(v_a_610_) == 1)
{
lean_object* v_val_614_; uint64_t v___x_615_; uint64_t v___x_616_; uint8_t v___x_617_; 
v_val_614_ = lean_ctor_get(v_a_610_, 0);
lean_inc(v_val_614_);
lean_dec_ref_known(v_a_610_, 1);
v___x_615_ = lean_unbox_uint64(v_val_608_);
lean_dec(v_val_608_);
v___x_616_ = lean_unbox_uint64(v_val_614_);
lean_dec(v_val_614_);
v___x_617_ = lean_int64_dec_eq(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___closed__44));
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_618_);
v___x_620_ = v___x_612_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
else
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_box(0);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_622_);
v___x_624_ = v___x_612_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_628_; 
lean_dec(v_a_610_);
lean_dec(v_val_608_);
v___x_626_ = lean_box(0);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_626_);
v___x_628_ = v___x_612_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_val_608_);
v_a_631_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_609_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_609_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v___x_639_; lean_object* v___x_641_; 
lean_dec(v_a_604_);
lean_dec_ref(v_b_184_);
v___x_639_ = lean_box(0);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_639_);
v___x_641_ = v___x_606_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref(v_b_184_);
v_a_644_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_603_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_603_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_652_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_570_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_570_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_660_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_537_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_537_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_668_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_504_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_504_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_676_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_471_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_471_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_684_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_438_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_438_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_692_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_405_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_405_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
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
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_700_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_372_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_372_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_709_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_332_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_332_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_718_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_292_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_292_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
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
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_726_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_259_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_259_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_734_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_221_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_221_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
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
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_b_184_);
lean_dec_ref(v_a_183_);
v_a_742_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_190_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_190_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f___boxed(lean_object* v_a_750_, lean_object* v_b_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f(v_a_750_, v_b_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
return v_res_757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__3(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = l_Lean_Level_ofNat(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__4(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_box(0);
v___x_766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__3, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__3);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__5(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__4, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__4);
v___x_769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__2));
v___x_770_ = l_Lean_mkConst(v___x_769_, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__8(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_box(0);
v___x_775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__7));
v___x_776_ = l_Lean_mkConst(v___x_775_, v___x_774_);
return v___x_776_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__11(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_box(0);
v___x_782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__10));
v___x_783_ = l_Lean_mkConst(v___x_782_, v___x_781_);
return v___x_783_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__12(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_784_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__11, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__11);
v___x_785_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__8, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__8_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__8);
v___x_786_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__5, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__5);
v___x_787_ = l_Lean_mkAppB(v___x_786_, v___x_785_, v___x_784_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f(lean_object* v_a_795_, lean_object* v_b_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; 
if (lean_obj_tag(v_a_795_) == 9)
{
lean_object* v_a_894_; 
v_a_894_ = lean_ctor_get(v_a_795_, 0);
if (lean_obj_tag(v_a_894_) == 1)
{
lean_inc_ref(v_a_894_);
lean_dec_ref_known(v_a_795_, 1);
if (lean_obj_tag(v_b_796_) == 9)
{
lean_object* v_a_895_; 
v_a_895_ = lean_ctor_get(v_b_796_, 0);
lean_inc_ref(v_a_895_);
lean_dec_ref_known(v_b_796_, 1);
if (lean_obj_tag(v_a_895_) == 1)
{
lean_object* v_val_896_; lean_object* v_val_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_935_; 
v_val_896_ = lean_ctor_get(v_a_894_, 0);
lean_inc_ref(v_val_896_);
lean_dec_ref_known(v_a_894_, 1);
v_val_897_ = lean_ctor_get(v_a_895_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v_a_895_);
if (v_isSharedCheck_935_ == 0)
{
v___x_899_ = v_a_895_;
v_isShared_900_ = v_isSharedCheck_935_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_val_897_);
lean_dec(v_a_895_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_935_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
uint8_t v___x_901_; 
v___x_901_ = lean_string_dec_eq(v_val_896_, v_val_897_);
if (v___x_901_ == 0)
{
uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v_env_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_902_ = 1;
v___x_903_ = lean_st_ref_get(v_a_800_);
v_env_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc_ref(v_env_904_);
lean_dec(v___x_903_);
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__16));
v___x_906_ = l_Lean_Environment_contains(v_env_904_, v___x_905_, v___x_902_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec_ref(v_val_897_);
lean_dec_ref(v_val_896_);
v___x_907_ = lean_box(0);
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 0);
lean_ctor_set(v___x_899_, 0, v___x_907_);
v___x_909_ = v___x_899_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
else
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Meta_mkStringLitNeProof___redArg(v_val_896_, v_val_897_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_922_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_922_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_922_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_922_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v_a_912_);
v___x_917_ = v___x_899_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_917_);
v___x_919_ = v___x_914_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_del_object(v___x_899_);
v_a_923_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_911_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_911_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_933_; 
lean_dec_ref(v_val_897_);
lean_dec_ref(v_val_896_);
v___x_931_ = lean_box(0);
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 0);
lean_ctor_set(v___x_899_, 0, v___x_931_);
v___x_933_ = v___x_899_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_dec_ref(v_a_895_);
lean_dec_ref_known(v_a_894_, 1);
goto v___jp_891_;
}
}
else
{
lean_dec_ref_known(v_a_894_, 1);
lean_dec_ref(v_b_796_);
goto v___jp_891_;
}
}
else
{
v___y_812_ = v_a_797_;
v___y_813_ = v_a_798_;
v___y_814_ = v_a_799_;
v___y_815_ = v_a_800_;
goto v___jp_811_;
}
}
else
{
v___y_812_ = v_a_797_;
v___y_813_ = v_a_798_;
v___y_814_ = v_a_799_;
v___y_815_ = v_a_800_;
goto v___jp_811_;
}
v___jp_802_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_box(0);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
v___jp_805_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc_ref(v___y_806_);
v___x_808_ = l_Lean_mkApp3(v___y_807_, v_a_795_, v_b_796_, v___y_806_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
v___jp_811_:
{
lean_object* v___x_816_; 
lean_inc_ref(v_a_795_);
v___x_816_ = l_Lean_Meta_normLitValue(v_a_795_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
lean_inc_ref(v_b_796_);
v___x_818_ = l_Lean_Meta_normLitValue(v_b_796_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; uint8_t v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = lean_expr_eqv(v_a_817_, v_a_795_);
lean_dec(v_a_817_);
if (v___x_820_ == 0)
{
lean_dec(v_a_819_);
lean_dec_ref(v_b_796_);
lean_dec_ref(v_a_795_);
goto v___jp_802_;
}
else
{
uint8_t v___x_821_; 
v___x_821_ = lean_expr_eqv(v_a_819_, v_b_796_);
lean_dec(v_a_819_);
if (v___x_821_ == 0)
{
lean_dec_ref(v_b_796_);
lean_dec_ref(v_a_795_);
goto v___jp_802_;
}
else
{
lean_object* v___x_822_; 
lean_inc_ref(v_b_796_);
lean_inc_ref(v_a_795_);
v___x_822_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f_neThm_x3f(v_a_795_, v_b_796_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_866_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_866_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_866_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_866_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
if (lean_obj_tag(v_a_823_) == 1)
{
lean_object* v_val_827_; lean_object* v___x_828_; lean_object* v_env_829_; uint8_t v___x_830_; 
v_val_827_ = lean_ctor_get(v_a_823_, 0);
lean_inc_n(v_val_827_, 2);
lean_dec_ref_known(v_a_823_, 1);
v___x_828_ = lean_st_ref_get(v___y_815_);
v_env_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc_ref(v_env_829_);
lean_dec(v___x_828_);
v___x_830_ = l_Lean_Environment_contains(v_env_829_, v_val_827_, v___x_820_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_833_; 
lean_dec(v_val_827_);
lean_dec_ref(v_b_796_);
lean_dec_ref(v_a_795_);
v___x_831_ = lean_box(0);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_831_);
v___x_833_ = v___x_825_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_del_object(v___x_825_);
v___x_835_ = lean_box(0);
v___x_836_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__12, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___closed__12);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc_ref(v_a_795_);
v___x_837_ = lean_infer_type(v_a_795_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = l_Lean_Meta_whnfR(v_a_838_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; uint8_t v___x_841_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v___x_841_ = l_Lean_Expr_isApp(v_a_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
lean_dec(v_a_840_);
v___x_842_ = l_Lean_mkConst(v_val_827_, v___x_835_);
v___y_806_ = v___x_836_;
v___y_807_ = v___x_842_;
goto v___jp_805_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = l_Lean_mkConst(v_val_827_, v___x_835_);
v___x_844_ = l_Lean_Expr_appArg_x21(v_a_840_);
lean_dec(v_a_840_);
v___x_845_ = l_Lean_Expr_app___override(v___x_843_, v___x_844_);
v___y_806_ = v___x_836_;
v___y_807_ = v___x_845_;
goto v___jp_805_;
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_val_827_);
lean_dec_ref(v_b_796_);
lean_dec_ref(v_a_795_);
v_a_846_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_839_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_839_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_val_827_);
lean_dec_ref(v_b_796_);
lean_dec_ref(v_a_795_);
v_a_854_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_837_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_837_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
else
{
lean_object* v___x_862_; lean_object* v___x_864_; 
lean_dec(v_a_823_);
lean_dec_ref(v_b_796_);
lean_dec_ref(v_a_795_);
v___x_862_ = lean_box(0);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_862_);
v___x_864_ = v___x_825_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
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
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref(v_b_796_);
lean_dec_ref(v_a_795_);
v_a_867_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_822_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_822_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_a_817_);
lean_dec_ref(v_b_796_);
lean_dec_ref(v_a_795_);
v_a_875_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_818_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_818_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v_b_796_);
lean_dec_ref(v_a_795_);
v_a_883_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_816_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_816_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
v___jp_891_:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_box(0);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f___boxed(lean_object* v_a_936_, lean_object* v_b_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f(v_a_936_, v_b_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Meta_saveState___redArg(v___y_946_, v___y_948_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_952_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
v___x_952_ = lean_apply_5(v_x_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, lean_box(0));
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_a_951_);
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_961_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v_a_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_992_; 
v_a_962_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_992_ == 0)
{
v___x_964_ = v___x_952_;
v_isShared_965_ = v_isSharedCheck_992_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_952_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_992_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
uint8_t v___x_966_; 
v___x_966_ = l_Lean_Exception_isInterrupt(v_a_962_);
if (v___x_966_ == 0)
{
uint8_t v___x_967_; 
lean_inc(v_a_962_);
v___x_967_ = l_Lean_Exception_isRuntime(v_a_962_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
lean_del_object(v___x_964_);
lean_dec(v_a_962_);
v___x_968_ = l_Lean_Meta_SavedState_restore___redArg(v_a_951_, v___y_946_, v___y_948_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_976_; 
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_968_, 0);
lean_dec(v_unused_977_);
v___x_970_ = v___x_968_;
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
else
{
lean_dec(v___x_968_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_box(0);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_a_978_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_968_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_968_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v___x_987_; 
lean_dec(v_a_951_);
if (v_isShared_965_ == 0)
{
v___x_987_ = v___x_964_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_962_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
lean_object* v___x_990_; 
lean_dec(v_a_951_);
if (v_isShared_965_ == 0)
{
v___x_990_ = v___x_964_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_962_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v_x_944_);
v_a_993_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_950_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_950_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg___boxed(lean_object* v_x_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(lean_object* v_00_u03b1_1008_, lean_object* v_x_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_x_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(v_00_u03b1_1016_, v_x_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(lean_object* v_msgData_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v_env_1031_; uint8_t v___x_1032_; lean_object* v_env_1033_; lean_object* v___x_1034_; lean_object* v_toCold_1035_; lean_object* v_mctx_1036_; lean_object* v_lctx_1037_; lean_object* v_options_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1030_ = lean_st_ref_get(v___y_1028_);
v_env_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc_ref(v_env_1031_);
lean_dec(v___x_1030_);
v___x_1032_ = 0;
v_env_1033_ = l_Lean_Environment_setRecordingDeps(v_env_1031_, v___x_1032_);
v___x_1034_ = lean_st_ref_get(v___y_1026_);
v_toCold_1035_ = lean_ctor_get(v___y_1027_, 0);
v_mctx_1036_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_ref(v_mctx_1036_);
lean_dec(v___x_1034_);
v_lctx_1037_ = lean_ctor_get(v___y_1025_, 2);
v_options_1038_ = lean_ctor_get(v_toCold_1035_, 2);
lean_inc_ref(v_options_1038_);
lean_inc_ref(v_lctx_1037_);
v___x_1039_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1039_, 0, v_env_1033_);
lean_ctor_set(v___x_1039_, 1, v_mctx_1036_);
lean_ctor_set(v___x_1039_, 2, v_lctx_1037_);
lean_ctor_set(v___x_1039_, 3, v_options_1038_);
v___x_1040_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v_msgData_1024_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1___boxed(lean_object* v_msgData_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msgData_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(lean_object* v_msg_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_ref_1055_; lean_object* v___x_1056_; lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1065_; 
v_ref_1055_ = lean_ctor_get(v___y_1052_, 2);
v___x_1056_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msg_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1065_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1065_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_inc(v_ref_1055_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_ref_1055_);
lean_ctor_set(v___x_1061_, 1, v_a_1057_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 1);
lean_ctor_set(v___x_1059_, 0, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg___boxed(lean_object* v_msg_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1072_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(lean_object* v_mvarId_1076_, lean_object* v_eqFVarId_1077_, lean_object* v_subst_1078_, lean_object* v_acyclic_1079_, lean_object* v_eqDecl_1080_, lean_object* v_a_1081_, lean_object* v_b_1082_, uint8_t v_symm_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1089_ = 1;
v___x_1090_ = lean_box(v_symm_1083_);
v___x_1091_ = lean_box(v___x_1089_);
v___x_1092_ = lean_box(v___x_1089_);
lean_inc(v_subst_1078_);
lean_inc(v_eqFVarId_1077_);
lean_inc(v_mvarId_1076_);
v___x_1093_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_1093_, 0, v_mvarId_1076_);
lean_closure_set(v___x_1093_, 1, v_eqFVarId_1077_);
lean_closure_set(v___x_1093_, 2, v___x_1090_);
lean_closure_set(v___x_1093_, 3, v_subst_1078_);
lean_closure_set(v___x_1093_, 4, v___x_1091_);
lean_closure_set(v___x_1093_, 5, v___x_1092_);
v___x_1094_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v___x_1093_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1170_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1170_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1170_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
if (lean_obj_tag(v_a_1095_) == 1)
{
lean_object* v_val_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v_b_1082_);
lean_dec_ref(v_a_1081_);
lean_dec_ref(v_acyclic_1079_);
lean_dec(v_subst_1078_);
lean_dec(v_eqFVarId_1077_);
lean_dec(v_mvarId_1076_);
v_val_1099_ = lean_ctor_get(v_a_1095_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_a_1095_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1101_ = v_a_1095_;
v_isShared_1102_ = v_isSharedCheck_1113_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_val_1099_);
lean_dec(v_a_1095_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1113_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v_fst_1103_ = lean_ctor_get(v_val_1099_, 0);
lean_inc(v_fst_1103_);
v_snd_1104_ = lean_ctor_get(v_val_1099_, 1);
lean_inc(v_snd_1104_);
lean_dec(v_val_1099_);
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1106_, 0, v_snd_1104_);
lean_ctor_set(v___x_1106_, 1, v_fst_1103_);
lean_ctor_set(v___x_1106_, 2, v___x_1105_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1106_);
v___x_1108_ = v___x_1101_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1108_);
v___x_1110_ = v___x_1097_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v___x_1114_; 
lean_del_object(v___x_1097_);
lean_dec(v_a_1095_);
v___x_1114_ = l_Lean_Meta_isExprDefEq(v_a_1081_, v_b_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; uint8_t v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = lean_unbox(v_a_1115_);
lean_dec(v_a_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec(v_subst_1078_);
v___x_1117_ = l_Lean_mkFVar(v_eqFVarId_1077_);
lean_inc(v_a_1087_);
lean_inc_ref(v_a_1086_);
lean_inc(v_a_1085_);
lean_inc_ref(v_a_1084_);
v___x_1118_ = lean_apply_7(v_acyclic_1079_, v_mvarId_1076_, v___x_1117_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, lean_box(0));
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1133_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1133_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1133_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_unbox(v_a_1119_);
lean_dec(v_a_1119_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_del_object(v___x_1121_);
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_1125_ = l_Lean_LocalDecl_type(v_eqDecl_1080_);
v___x_1126_ = l_Lean_indentExpr(v___x_1125_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1124_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_1127_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = lean_box(0);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1129_);
v___x_1131_ = v___x_1121_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
v_a_1134_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1118_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1118_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v___x_1142_; 
lean_dec_ref(v_acyclic_1079_);
v___x_1142_ = l_Lean_MVarId_clear(v_mvarId_1076_, v_eqFVarId_1077_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1153_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1153_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1153_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1148_, 0, v_a_1143_);
lean_ctor_set(v___x_1148_, 1, v_subst_1078_);
lean_ctor_set(v___x_1148_, 2, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1149_);
v___x_1151_ = v___x_1145_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_subst_1078_);
v_a_1154_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1142_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1142_);
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
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v_acyclic_1079_);
lean_dec(v_subst_1078_);
lean_dec(v_eqFVarId_1077_);
lean_dec(v_mvarId_1076_);
v_a_1162_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1114_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1114_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
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
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_b_1082_);
lean_dec_ref(v_a_1081_);
lean_dec_ref(v_acyclic_1079_);
lean_dec(v_subst_1078_);
lean_dec(v_eqFVarId_1077_);
lean_dec(v_mvarId_1076_);
v_a_1171_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1094_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1094_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___boxed(lean_object* v_mvarId_1179_, lean_object* v_eqFVarId_1180_, lean_object* v_subst_1181_, lean_object* v_acyclic_1182_, lean_object* v_eqDecl_1183_, lean_object* v_a_1184_, lean_object* v_b_1185_, lean_object* v_symm_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v_symm_boxed_1192_; lean_object* v_res_1193_; 
v_symm_boxed_1192_ = lean_unbox(v_symm_1186_);
v_res_1193_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1179_, v_eqFVarId_1180_, v_subst_1181_, v_acyclic_1182_, v_eqDecl_1183_, v_a_1184_, v_b_1185_, v_symm_boxed_1192_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec_ref(v_eqDecl_1183_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(lean_object* v_00_u03b1_1194_, lean_object* v_msg_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___boxed(lean_object* v_00_u03b1_1202_, lean_object* v_msg_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(v_00_u03b1_1202_, v_msg_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_){
_start:
{
lean_object* v_ks_1214_; lean_object* v_vs_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1239_; 
v_ks_1214_ = lean_ctor_get(v_x_1210_, 0);
v_vs_1215_ = lean_ctor_get(v_x_1210_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_x_1210_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1217_ = v_x_1210_;
v_isShared_1218_ = v_isSharedCheck_1239_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_vs_1215_);
lean_inc(v_ks_1214_);
lean_dec(v_x_1210_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1239_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = lean_array_get_size(v_ks_1214_);
v___x_1220_ = lean_nat_dec_lt(v_x_1211_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
lean_dec(v_x_1211_);
v___x_1221_ = lean_array_push(v_ks_1214_, v_x_1212_);
v___x_1222_ = lean_array_push(v_vs_1215_, v_x_1213_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v___x_1222_);
lean_ctor_set(v___x_1217_, 0, v___x_1221_);
v___x_1224_ = v___x_1217_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
else
{
lean_object* v_k_x27_1226_; uint8_t v___x_1227_; 
v_k_x27_1226_ = lean_array_fget_borrowed(v_ks_1214_, v_x_1211_);
v___x_1227_ = l_Lean_instBEqMVarId_beq(v_x_1212_, v_k_x27_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1229_; 
if (v_isShared_1218_ == 0)
{
v___x_1229_ = v___x_1217_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_ks_1214_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_vs_1215_);
v___x_1229_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_add(v_x_1211_, v___x_1230_);
lean_dec(v_x_1211_);
v_x_1210_ = v___x_1229_;
v_x_1211_ = v___x_1231_;
goto _start;
}
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1234_ = lean_array_fset(v_ks_1214_, v_x_1211_, v_x_1212_);
v___x_1235_ = lean_array_fset(v_vs_1215_, v_x_1211_, v_x_1213_);
lean_dec(v_x_1211_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v___x_1235_);
lean_ctor_set(v___x_1217_, 0, v___x_1234_);
v___x_1237_ = v___x_1217_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1240_, lean_object* v_k_1241_, lean_object* v_v_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1240_, v___x_1243_, v_k_1241_, v_v_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1246_, size_t v_x_1247_, size_t v_x_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
lean_object* v_es_1251_; size_t v___x_1252_; size_t v___x_1253_; lean_object* v_j_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_es_1251_ = lean_ctor_get(v_x_1246_, 0);
v___x_1252_ = ((size_t)31ULL);
v___x_1253_ = lean_usize_land(v_x_1247_, v___x_1252_);
v_j_1254_ = lean_usize_to_nat(v___x_1253_);
v___x_1255_ = lean_array_get_size(v_es_1251_);
v___x_1256_ = lean_nat_dec_lt(v_j_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_dec(v_j_1254_);
lean_dec(v_x_1250_);
lean_dec(v_x_1249_);
return v_x_1246_;
}
else
{
lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1295_; 
lean_inc_ref(v_es_1251_);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_x_1246_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v_x_1246_, 0);
lean_dec(v_unused_1296_);
v___x_1258_ = v_x_1246_;
v_isShared_1259_ = v_isSharedCheck_1295_;
goto v_resetjp_1257_;
}
else
{
lean_dec(v_x_1246_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1295_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_v_1260_; lean_object* v___x_1261_; lean_object* v_xs_x27_1262_; lean_object* v___y_1264_; 
v_v_1260_ = lean_array_fget(v_es_1251_, v_j_1254_);
v___x_1261_ = lean_box(0);
v_xs_x27_1262_ = lean_array_fset(v_es_1251_, v_j_1254_, v___x_1261_);
switch(lean_obj_tag(v_v_1260_))
{
case 0:
{
lean_object* v_key_1269_; lean_object* v_val_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1280_; 
v_key_1269_ = lean_ctor_get(v_v_1260_, 0);
v_val_1270_ = lean_ctor_get(v_v_1260_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_v_1260_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1272_ = v_v_1260_;
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_val_1270_);
lean_inc(v_key_1269_);
lean_dec(v_v_1260_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
uint8_t v___x_1274_; 
v___x_1274_ = l_Lean_instBEqMVarId_beq(v_x_1249_, v_key_1269_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_del_object(v___x_1272_);
v___x_1275_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1269_, v_val_1270_, v_x_1249_, v_x_1250_);
v___x_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
v___y_1264_ = v___x_1276_;
goto v___jp_1263_;
}
else
{
lean_object* v___x_1278_; 
lean_dec(v_val_1270_);
lean_dec(v_key_1269_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v_x_1250_);
lean_ctor_set(v___x_1272_, 0, v_x_1249_);
v___x_1278_ = v___x_1272_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_x_1249_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_x_1250_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
v___y_1264_ = v___x_1278_;
goto v___jp_1263_;
}
}
}
}
case 1:
{
lean_object* v_node_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1293_; 
v_node_1281_ = lean_ctor_get(v_v_1260_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_v_1260_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1283_ = v_v_1260_;
v_isShared_1284_ = v_isSharedCheck_1293_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_node_1281_);
lean_dec(v_v_1260_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1293_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
size_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1285_ = ((size_t)5ULL);
v___x_1286_ = lean_usize_shift_right(v_x_1247_, v___x_1285_);
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = lean_usize_add(v_x_1248_, v___x_1287_);
v___x_1289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg(v_node_1281_, v___x_1286_, v___x_1288_, v_x_1249_, v_x_1250_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1289_);
v___x_1291_ = v___x_1283_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
v___y_1264_ = v___x_1291_;
goto v___jp_1263_;
}
}
}
default: 
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_x_1249_);
lean_ctor_set(v___x_1294_, 1, v_x_1250_);
v___y_1264_ = v___x_1294_;
goto v___jp_1263_;
}
}
v___jp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_array_fset(v_xs_x27_1262_, v_j_1254_, v___y_1264_);
lean_dec(v_j_1254_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1265_);
v___x_1267_ = v___x_1258_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
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
}
else
{
lean_object* v_ks_1297_; lean_object* v_vs_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1316_; 
v_ks_1297_ = lean_ctor_get(v_x_1246_, 0);
v_vs_1298_ = lean_ctor_get(v_x_1246_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_x_1246_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1300_ = v_x_1246_;
v_isShared_1301_ = v_isSharedCheck_1316_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_vs_1298_);
lean_inc(v_ks_1297_);
lean_dec(v_x_1246_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1316_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_ks_1297_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_vs_1298_);
v___x_1303_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v_newNode_1304_; size_t v___x_1305_; uint8_t v___x_1306_; 
v_newNode_1304_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1303_, v_x_1249_, v_x_1250_);
v___x_1305_ = ((size_t)7ULL);
v___x_1306_ = lean_usize_dec_le(v___x_1305_, v_x_1248_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1307_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1304_);
v___x_1308_ = lean_unsigned_to_nat(4u);
v___x_1309_ = lean_nat_dec_lt(v___x_1307_, v___x_1308_);
lean_dec(v___x_1307_);
if (v___x_1309_ == 0)
{
lean_object* v_ks_1310_; lean_object* v_vs_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_ks_1310_ = lean_ctor_get(v_newNode_1304_, 0);
lean_inc_ref(v_ks_1310_);
v_vs_1311_ = lean_ctor_get(v_newNode_1304_, 1);
lean_inc_ref(v_vs_1311_);
lean_dec_ref(v_newNode_1304_);
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1314_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1248_, v_ks_1310_, v_vs_1311_, v___x_1312_, v___x_1313_);
lean_dec_ref(v_vs_1311_);
lean_dec_ref(v_ks_1310_);
return v___x_1314_;
}
else
{
return v_newNode_1304_;
}
}
else
{
return v_newNode_1304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1317_, lean_object* v_keys_1318_, lean_object* v_vals_1319_, lean_object* v_i_1320_, lean_object* v_entries_1321_){
_start:
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = lean_array_get_size(v_keys_1318_);
v___x_1323_ = lean_nat_dec_lt(v_i_1320_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_dec(v_i_1320_);
return v_entries_1321_;
}
else
{
lean_object* v_k_1324_; lean_object* v_v_1325_; uint64_t v___x_1326_; size_t v_h_1327_; size_t v___x_1328_; lean_object* v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v_h_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_k_1324_ = lean_array_fget_borrowed(v_keys_1318_, v_i_1320_);
v_v_1325_ = lean_array_fget_borrowed(v_vals_1319_, v_i_1320_);
v___x_1326_ = l_Lean_instHashableMVarId_hash(v_k_1324_);
v_h_1327_ = lean_uint64_to_usize(v___x_1326_);
v___x_1328_ = ((size_t)5ULL);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = ((size_t)1ULL);
v___x_1331_ = lean_usize_sub(v_depth_1317_, v___x_1330_);
v___x_1332_ = lean_usize_mul(v___x_1328_, v___x_1331_);
v_h_1333_ = lean_usize_shift_right(v_h_1327_, v___x_1332_);
v___x_1334_ = lean_nat_add(v_i_1320_, v___x_1329_);
lean_dec(v_i_1320_);
lean_inc(v_v_1325_);
lean_inc(v_k_1324_);
v___x_1335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg(v_entries_1321_, v_h_1333_, v_depth_1317_, v_k_1324_, v_v_1325_);
v_i_1320_ = v___x_1334_;
v_entries_1321_ = v___x_1335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1337_, lean_object* v_keys_1338_, lean_object* v_vals_1339_, lean_object* v_i_1340_, lean_object* v_entries_1341_){
_start:
{
size_t v_depth_boxed_1342_; lean_object* v_res_1343_; 
v_depth_boxed_1342_ = lean_unbox_usize(v_depth_1337_);
lean_dec(v_depth_1337_);
v_res_1343_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1342_, v_keys_1338_, v_vals_1339_, v_i_1340_, v_entries_1341_);
lean_dec_ref(v_vals_1339_);
lean_dec_ref(v_keys_1338_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1344_, lean_object* v_x_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
size_t v_x_3385__boxed_1349_; size_t v_x_3386__boxed_1350_; lean_object* v_res_1351_; 
v_x_3385__boxed_1349_ = lean_unbox_usize(v_x_1345_);
lean_dec(v_x_1345_);
v_x_3386__boxed_1350_ = lean_unbox_usize(v_x_1346_);
lean_dec(v_x_1346_);
v_res_1351_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg(v_x_1344_, v_x_3385__boxed_1349_, v_x_3386__boxed_1350_, v_x_1347_, v_x_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0___redArg(lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v_x_1354_){
_start:
{
uint64_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1355_ = l_Lean_instHashableMVarId_hash(v_x_1353_);
v___x_1356_ = lean_uint64_to_usize(v___x_1355_);
v___x_1357_ = ((size_t)1ULL);
v___x_1358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg(v_x_1352_, v___x_1356_, v___x_1357_, v_x_1353_, v_x_1354_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___redArg(lean_object* v_mvarId_1359_, lean_object* v_val_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v_mctx_1364_; lean_object* v_cache_1365_; lean_object* v_zetaDeltaFVarIds_1366_; lean_object* v_postponed_1367_; lean_object* v_diag_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1397_; 
v___x_1363_ = lean_st_ref_take(v___y_1361_);
v_mctx_1364_ = lean_ctor_get(v___x_1363_, 0);
v_cache_1365_ = lean_ctor_get(v___x_1363_, 1);
v_zetaDeltaFVarIds_1366_ = lean_ctor_get(v___x_1363_, 2);
v_postponed_1367_ = lean_ctor_get(v___x_1363_, 3);
v_diag_1368_ = lean_ctor_get(v___x_1363_, 4);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1370_ = v___x_1363_;
v_isShared_1371_ = v_isSharedCheck_1397_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_diag_1368_);
lean_inc(v_postponed_1367_);
lean_inc(v_zetaDeltaFVarIds_1366_);
lean_inc(v_cache_1365_);
lean_inc(v_mctx_1364_);
lean_dec(v___x_1363_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1397_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v_depth_1372_; lean_object* v_levelAssignDepth_1373_; lean_object* v_lmvarCounter_1374_; lean_object* v_mvarCounter_1375_; lean_object* v_lDecls_1376_; lean_object* v_decls_1377_; lean_object* v_userNames_1378_; lean_object* v_lAssignment_1379_; lean_object* v_eAssignment_1380_; lean_object* v_dAssignment_1381_; lean_object* v_instanceTypedMVars_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1396_; 
v_depth_1372_ = lean_ctor_get(v_mctx_1364_, 0);
v_levelAssignDepth_1373_ = lean_ctor_get(v_mctx_1364_, 1);
v_lmvarCounter_1374_ = lean_ctor_get(v_mctx_1364_, 2);
v_mvarCounter_1375_ = lean_ctor_get(v_mctx_1364_, 3);
v_lDecls_1376_ = lean_ctor_get(v_mctx_1364_, 4);
v_decls_1377_ = lean_ctor_get(v_mctx_1364_, 5);
v_userNames_1378_ = lean_ctor_get(v_mctx_1364_, 6);
v_lAssignment_1379_ = lean_ctor_get(v_mctx_1364_, 7);
v_eAssignment_1380_ = lean_ctor_get(v_mctx_1364_, 8);
v_dAssignment_1381_ = lean_ctor_get(v_mctx_1364_, 9);
v_instanceTypedMVars_1382_ = lean_ctor_get(v_mctx_1364_, 10);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_mctx_1364_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1384_ = v_mctx_1364_;
v_isShared_1385_ = v_isSharedCheck_1396_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_instanceTypedMVars_1382_);
lean_inc(v_dAssignment_1381_);
lean_inc(v_eAssignment_1380_);
lean_inc(v_lAssignment_1379_);
lean_inc(v_userNames_1378_);
lean_inc(v_decls_1377_);
lean_inc(v_lDecls_1376_);
lean_inc(v_mvarCounter_1375_);
lean_inc(v_lmvarCounter_1374_);
lean_inc(v_levelAssignDepth_1373_);
lean_inc(v_depth_1372_);
lean_dec(v_mctx_1364_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1396_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0___redArg(v_eAssignment_1380_, v_mvarId_1359_, v_val_1360_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 8, v___x_1387_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_depth_1372_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_levelAssignDepth_1373_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_lmvarCounter_1374_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_mvarCounter_1375_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v_lDecls_1376_);
lean_ctor_set(v_reuseFailAlloc_1395_, 5, v_decls_1377_);
lean_ctor_set(v_reuseFailAlloc_1395_, 6, v_userNames_1378_);
lean_ctor_set(v_reuseFailAlloc_1395_, 7, v_lAssignment_1379_);
lean_ctor_set(v_reuseFailAlloc_1395_, 8, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1395_, 9, v_dAssignment_1381_);
lean_ctor_set(v_reuseFailAlloc_1395_, 10, v_instanceTypedMVars_1382_);
v___x_1389_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1389_);
v___x_1391_ = v___x_1370_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_cache_1365_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_zetaDeltaFVarIds_1366_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_postponed_1367_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_diag_1368_);
v___x_1391_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_st_ref_put(v___y_1361_, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1386_);
return v___x_1393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___redArg___boxed(lean_object* v_mvarId_1398_, lean_object* v_val_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___redArg(v_mvarId_1398_, v_val_1399_, v___y_1400_);
lean_dec(v___y_1400_);
return v_res_1402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0));
v___x_1405_ = l_Lean_stringToMessageData(v___x_1404_);
return v___x_1405_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2));
v___x_1408_ = l_Lean_stringToMessageData(v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(lean_object* v_mvarId_1409_, lean_object* v_eqFVarId_1410_, lean_object* v_subst_1411_, lean_object* v_caseName_x3f_1412_, lean_object* v_eqDecl_1413_, lean_object* v_injectionOffset_x3f_1414_, lean_object* v_a_1415_, lean_object* v_b_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v___y_1423_; lean_object* v___y_1424_; uint8_t v_a_1468_; lean_object* v___x_1508_; 
lean_inc_ref(v_b_1416_);
lean_inc_ref(v_a_1415_);
v___x_1508_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_mkLitNeProof_x3f(v_a_1415_, v_b_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
if (lean_obj_tag(v_a_1509_) == 1)
{
lean_object* v_val_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_a_1415_);
lean_dec_ref(v_injectionOffset_x3f_1414_);
lean_dec(v_caseName_x3f_1412_);
lean_dec(v_subst_1411_);
v_val_1510_ = lean_ctor_get(v_a_1509_, 0);
lean_inc(v_val_1510_);
lean_dec_ref_known(v_a_1509_, 1);
lean_inc(v_mvarId_1409_);
v___x_1511_ = l_Lean_MVarId_getType(v_mvarId_1409_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = l_Lean_mkFVar(v_eqFVarId_1410_);
v___x_1514_ = l_Lean_Meta_mkAbsurd(v_a_1512_, v___x_1513_, v_val_1510_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1524_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___redArg(v_mvarId_1409_, v_a_1515_, v_a_1418_);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v___x_1516_, 0);
lean_dec(v_unused_1525_);
v___x_1518_ = v___x_1516_;
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v___x_1516_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_box(0);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_mvarId_1409_);
v_a_1526_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1514_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1514_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_val_1510_);
lean_dec(v_eqFVarId_1410_);
lean_dec(v_mvarId_1409_);
v_a_1534_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1511_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1511_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
lean_object* v___x_1542_; 
lean_dec(v_a_1509_);
lean_inc(v_a_1420_);
lean_inc_ref(v_a_1419_);
lean_inc(v_a_1418_);
lean_inc_ref(v_a_1417_);
lean_inc_ref(v_b_1416_);
lean_inc_ref(v_a_1415_);
v___x_1542_ = lean_apply_7(v_injectionOffset_x3f_1414_, v_a_1415_, v_b_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, lean_box(0));
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1600_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1600_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1600_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
if (lean_obj_tag(v_a_1543_) == 1)
{
lean_object* v_val_1547_; lean_object* v___x_1549_; 
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_caseName_x3f_1412_);
lean_dec(v_subst_1411_);
lean_dec(v_eqFVarId_1410_);
lean_dec(v_mvarId_1409_);
v_val_1547_ = lean_ctor_get(v_a_1543_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v_a_1543_, 1);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v_val_1547_);
v___x_1549_ = v___x_1545_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_val_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
else
{
lean_object* v___x_1551_; 
lean_del_object(v___x_1545_);
lean_dec(v_a_1543_);
lean_inc_ref(v_a_1415_);
v___x_1551_ = l_Lean_Meta_isConstructorApp(v_a_1415_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; uint8_t v___x_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = lean_unbox(v_a_1552_);
if (v___x_1553_ == 0)
{
uint8_t v___x_1554_; 
v___x_1554_ = lean_unbox(v_a_1552_);
lean_dec(v_a_1552_);
v_a_1468_ = v___x_1554_;
goto v___jp_1467_;
}
else
{
lean_object* v___x_1555_; 
lean_dec(v_a_1552_);
lean_inc_ref(v_b_1416_);
v___x_1555_ = l_Lean_Meta_isConstructorApp(v_b_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; uint8_t v___x_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1557_ = lean_unbox(v_a_1556_);
if (v___x_1557_ == 0)
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_unbox(v_a_1556_);
lean_dec(v_a_1556_);
v_a_1468_ = v___x_1558_;
goto v___jp_1467_;
}
else
{
lean_object* v___x_1559_; 
lean_dec(v_a_1556_);
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_caseName_x3f_1412_);
v___x_1559_ = l_Lean_Meta_injectionCore(v_mvarId_1409_, v_eqFVarId_1410_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1575_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1575_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1575_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
if (lean_obj_tag(v_a_1560_) == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
lean_dec(v_subst_1411_);
v___x_1564_ = lean_box(0);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
else
{
lean_object* v_mvarId_1568_; lean_object* v_numNewEqs_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v_mvarId_1568_ = lean_ctor_get(v_a_1560_, 0);
lean_inc(v_mvarId_1568_);
v_numNewEqs_1569_ = lean_ctor_get(v_a_1560_, 1);
lean_inc(v_numNewEqs_1569_);
lean_dec_ref_known(v_a_1560_, 2);
v___x_1570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1570_, 0, v_mvarId_1568_);
lean_ctor_set(v___x_1570_, 1, v_subst_1411_);
lean_ctor_set(v___x_1570_, 2, v_numNewEqs_1569_);
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1571_);
v___x_1573_ = v___x_1562_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_subst_1411_);
v_a_1576_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1559_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1559_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_caseName_x3f_1412_);
lean_dec(v_subst_1411_);
lean_dec(v_eqFVarId_1410_);
lean_dec(v_mvarId_1409_);
v_a_1584_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1555_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1555_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_caseName_x3f_1412_);
lean_dec(v_subst_1411_);
lean_dec(v_eqFVarId_1410_);
lean_dec(v_mvarId_1409_);
v_a_1592_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1551_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1551_);
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
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_caseName_x3f_1412_);
lean_dec(v_subst_1411_);
lean_dec(v_eqFVarId_1410_);
lean_dec(v_mvarId_1409_);
v_a_1601_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1542_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1542_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_a_1415_);
lean_dec_ref(v_injectionOffset_x3f_1414_);
lean_dec(v_caseName_x3f_1412_);
lean_dec(v_subst_1411_);
lean_dec(v_eqFVarId_1410_);
lean_dec(v_mvarId_1409_);
v_a_1609_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1508_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1508_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
v___jp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_inc(v_eqFVarId_1410_);
v___x_1425_ = l_Lean_mkFVar(v_eqFVarId_1410_);
v___x_1426_ = l_Lean_Meta_mkEq(v___y_1424_, v___y_1423_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l_Lean_LocalDecl_userName(v_eqDecl_1413_);
v___x_1429_ = l_Lean_MVarId_assert(v_mvarId_1409_, v___x_1428_, v_a_1427_, v___x_1425_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = l_Lean_MVarId_clear(v_a_1430_, v_eqFVarId_1410_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1442_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1442_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1442_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1437_, 0, v_a_1432_);
lean_ctor_set(v___x_1437_, 1, v_subst_1411_);
lean_ctor_set(v___x_1437_, 2, v___x_1436_);
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1438_);
v___x_1440_ = v___x_1434_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_subst_1411_);
v_a_1443_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1431_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1431_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_subst_1411_);
lean_dec(v_eqFVarId_1410_);
v_a_1451_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1429_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1429_);
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
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec_ref(v___x_1425_);
lean_dec(v_subst_1411_);
lean_dec(v_eqFVarId_1410_);
lean_dec(v_mvarId_1409_);
v_a_1459_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1426_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1426_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
v___jp_1467_:
{
lean_object* v___x_1469_; 
lean_inc(v_a_1420_);
lean_inc_ref(v_a_1419_);
lean_inc(v_a_1418_);
lean_inc_ref(v_a_1417_);
lean_inc_ref(v_a_1415_);
v___x_1469_ = lean_whnf(v_a_1415_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
lean_inc(v_a_1420_);
lean_inc_ref(v_a_1419_);
lean_inc(v_a_1418_);
lean_inc_ref(v_a_1417_);
lean_inc_ref(v_b_1416_);
v___x_1471_ = lean_whnf(v_b_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; uint8_t v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = lean_expr_eqv(v_a_1470_, v_a_1415_);
lean_dec_ref(v_a_1415_);
if (v___x_1473_ == 0)
{
lean_dec_ref(v_b_1416_);
lean_dec(v_caseName_x3f_1412_);
v___y_1423_ = v_a_1472_;
v___y_1424_ = v_a_1470_;
goto v___jp_1422_;
}
else
{
if (v_a_1468_ == 0)
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_expr_eqv(v_a_1472_, v_b_1416_);
lean_dec_ref(v_b_1416_);
if (v___x_1474_ == 0)
{
lean_dec(v_caseName_x3f_1412_);
v___y_1423_ = v_a_1472_;
v___y_1424_ = v_a_1470_;
goto v___jp_1422_;
}
else
{
lean_dec(v_a_1472_);
lean_dec(v_a_1470_);
lean_dec(v_subst_1411_);
lean_dec(v_eqFVarId_1410_);
lean_dec(v_mvarId_1409_);
if (lean_obj_tag(v_caseName_x3f_1412_) == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_1476_ = l_Lean_LocalDecl_type(v_eqDecl_1413_);
v___x_1477_ = l_Lean_indentExpr(v___x_1476_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1475_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_1478_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
return v___x_1479_;
}
else
{
lean_object* v_val_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_val_1480_ = lean_ctor_get(v_caseName_x3f_1412_, 0);
lean_inc(v_val_1480_);
lean_dec_ref_known(v_caseName_x3f_1412_, 1);
v___x_1481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_1482_ = l_Lean_LocalDecl_type(v_eqDecl_1413_);
v___x_1483_ = l_Lean_indentExpr(v___x_1482_);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1481_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_MessageData_ofConstName(v_val_1480_, v_a_1468_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_1490_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
return v___x_1491_;
}
}
}
else
{
lean_dec_ref(v_b_1416_);
lean_dec(v_caseName_x3f_1412_);
v___y_1423_ = v_a_1472_;
v___y_1424_ = v_a_1470_;
goto v___jp_1422_;
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_a_1470_);
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_caseName_x3f_1412_);
lean_dec(v_subst_1411_);
lean_dec(v_eqFVarId_1410_);
lean_dec(v_mvarId_1409_);
v_a_1492_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1471_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1471_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_caseName_x3f_1412_);
lean_dec(v_subst_1411_);
lean_dec(v_eqFVarId_1410_);
lean_dec(v_mvarId_1409_);
v_a_1500_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1469_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1469_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___boxed(lean_object* v_mvarId_1617_, lean_object* v_eqFVarId_1618_, lean_object* v_subst_1619_, lean_object* v_caseName_x3f_1620_, lean_object* v_eqDecl_1621_, lean_object* v_injectionOffset_x3f_1622_, lean_object* v_a_1623_, lean_object* v_b_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_1617_, v_eqFVarId_1618_, v_subst_1619_, v_caseName_x3f_1620_, v_eqDecl_1621_, v_injectionOffset_x3f_1622_, v_a_1623_, v_b_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec_ref(v_eqDecl_1621_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0(lean_object* v_mvarId_1631_, lean_object* v_val_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___redArg(v_mvarId_1631_, v_val_1632_, v___y_1634_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___boxed(lean_object* v_mvarId_1639_, lean_object* v_val_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0(v_mvarId_1639_, v_val_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0(lean_object* v_00_u03b2_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0___redArg(v_x_1648_, v_x_1649_, v_x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1652_, lean_object* v_x_1653_, size_t v_x_1654_, size_t v_x_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___redArg(v_x_1653_, v_x_1654_, v_x_1655_, v_x_1656_, v_x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
size_t v_x_4039__boxed_1665_; size_t v_x_4040__boxed_1666_; lean_object* v_res_1667_; 
v_x_4039__boxed_1665_ = lean_unbox_usize(v_x_1661_);
lean_dec(v_x_1661_);
v_x_4040__boxed_1666_ = lean_unbox_usize(v_x_1662_);
lean_dec(v_x_1662_);
v_res_1667_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1(v_00_u03b2_1659_, v_x_1660_, v_x_4039__boxed_1665_, v_x_4040__boxed_1666_, v_x_1663_, v_x_1664_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1668_, lean_object* v_n_1669_, lean_object* v_k_1670_, lean_object* v_v_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1669_, v_k_1670_, v_v_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1673_, size_t v_depth_1674_, lean_object* v_keys_1675_, lean_object* v_vals_1676_, lean_object* v_heq_1677_, lean_object* v_i_1678_, lean_object* v_entries_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1674_, v_keys_1675_, v_vals_1676_, v_i_1678_, v_entries_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1681_, lean_object* v_depth_1682_, lean_object* v_keys_1683_, lean_object* v_vals_1684_, lean_object* v_heq_1685_, lean_object* v_i_1686_, lean_object* v_entries_1687_){
_start:
{
size_t v_depth_boxed_1688_; lean_object* v_res_1689_; 
v_depth_boxed_1688_ = lean_unbox_usize(v_depth_1682_);
lean_dec(v_depth_1682_);
v_res_1689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1681_, v_depth_boxed_1688_, v_keys_1683_, v_vals_1684_, v_heq_1685_, v_i_1686_, v_entries_1687_);
lean_dec_ref(v_vals_1684_);
lean_dec_ref(v_keys_1683_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1690_, lean_object* v_x_1691_, lean_object* v_x_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1691_, v_x_1692_, v_x_1693_, v_x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_unifyEq_x3f_spec__0(lean_object* v_x_1696_, lean_object* v_x_1697_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
if (lean_obj_tag(v_x_1697_) == 0)
{
uint8_t v___x_1698_; 
v___x_1698_ = 1;
return v___x_1698_;
}
else
{
uint8_t v___x_1699_; 
v___x_1699_ = 0;
return v___x_1699_;
}
}
else
{
if (lean_obj_tag(v_x_1697_) == 0)
{
uint8_t v___x_1700_; 
v___x_1700_ = 0;
return v___x_1700_;
}
else
{
lean_object* v_val_1701_; lean_object* v_val_1702_; uint8_t v___x_1703_; 
v_val_1701_ = lean_ctor_get(v_x_1696_, 0);
v_val_1702_ = lean_ctor_get(v_x_1697_, 0);
v___x_1703_ = lean_nat_dec_eq(v_val_1701_, v_val_1702_);
return v___x_1703_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_unifyEq_x3f_spec__0___boxed(lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
uint8_t v_res_1706_; lean_object* v_r_1707_; 
v_res_1706_ = l_instBEqOption_beq___at___00Lean_Meta_unifyEq_x3f_spec__0(v_x_1704_, v_x_1705_);
lean_dec(v_x_1705_);
lean_dec(v_x_1704_);
v_r_1707_ = lean_box(v_res_1706_);
return v_r_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(lean_object* v_e_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v___x_1711_; 
v___x_1711_ = l_Lean_Expr_hasMVar(v_e_1708_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v_e_1708_);
return v___x_1712_;
}
else
{
lean_object* v___x_1713_; lean_object* v_mctx_1714_; lean_object* v___x_1715_; lean_object* v_fst_1716_; lean_object* v_snd_1717_; lean_object* v___x_1718_; lean_object* v_cache_1719_; lean_object* v_zetaDeltaFVarIds_1720_; lean_object* v_postponed_1721_; lean_object* v_diag_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
v___x_1713_ = lean_st_ref_get(v___y_1709_);
v_mctx_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc_ref(v_mctx_1714_);
lean_dec(v___x_1713_);
v___x_1715_ = l_Lean_instantiateMVarsCore(v_mctx_1714_, v_e_1708_);
v_fst_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_fst_1716_);
v_snd_1717_ = lean_ctor_get(v___x_1715_, 1);
lean_inc(v_snd_1717_);
lean_dec_ref(v___x_1715_);
v___x_1718_ = lean_st_ref_take(v___y_1709_);
v_cache_1719_ = lean_ctor_get(v___x_1718_, 1);
v_zetaDeltaFVarIds_1720_ = lean_ctor_get(v___x_1718_, 2);
v_postponed_1721_ = lean_ctor_get(v___x_1718_, 3);
v_diag_1722_ = lean_ctor_get(v___x_1718_, 4);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; 
v_unused_1732_ = lean_ctor_get(v___x_1718_, 0);
lean_dec(v_unused_1732_);
v___x_1724_ = v___x_1718_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_diag_1722_);
lean_inc(v_postponed_1721_);
lean_inc(v_zetaDeltaFVarIds_1720_);
lean_inc(v_cache_1719_);
lean_dec(v___x_1718_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v_snd_1717_);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_snd_1717_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_cache_1719_);
lean_ctor_set(v_reuseFailAlloc_1730_, 2, v_zetaDeltaFVarIds_1720_);
lean_ctor_set(v_reuseFailAlloc_1730_, 3, v_postponed_1721_);
lean_ctor_set(v_reuseFailAlloc_1730_, 4, v_diag_1722_);
v___x_1727_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_st_ref_put(v___y_1709_, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_fst_1716_);
return v___x_1729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg___boxed(lean_object* v_e_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_e_1733_, v___y_1734_);
lean_dec(v___y_1734_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1(lean_object* v_e_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_e_1737_, v___y_1739_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___boxed(lean_object* v_e_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1(v_e_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(lean_object* v_mvarId_1751_, lean_object* v_x_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1751_, v_x_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1758_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1758_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg___boxed(lean_object* v_mvarId_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_1775_, v_x_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(lean_object* v_00_u03b1_1783_, lean_object* v_mvarId_1784_, lean_object* v_x_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_1784_, v_x_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___boxed(lean_object* v_00_u03b1_1792_, lean_object* v_mvarId_1793_, lean_object* v_x_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(v_00_u03b1_1792_, v_mvarId_1793_, v_x_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1800_;
}
}
static lean_object* _init_l_Lean_Meta_unifyEq_x3f___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = lean_box(0);
v___x_1820_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__5));
v___x_1821_ = l_Lean_mkConst(v___x_1820_, v___x_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0(lean_object* v_mvarId_1822_, lean_object* v_eqFVarId_1823_, uint8_t v___x_1824_, lean_object* v_a_1825_, lean_object* v_subst_1826_, lean_object* v_a_1827_, lean_object* v_b_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_hne_1835_; lean_object* v___x_1873_; lean_object* v_env_1874_; lean_object* v___x_1875_; lean_object* v_fst_1877_; lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; uint8_t v___x_1989_; 
v___x_1873_ = lean_st_ref_get(v___y_1832_);
v_env_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc_ref(v_env_1874_);
lean_dec(v___x_1873_);
v___x_1875_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__2));
v___x_1989_ = l_Lean_Environment_contains(v_env_1874_, v___x_1875_, v___x_1824_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec_ref(v_b_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v___x_1990_ = lean_box(0);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; 
lean_inc_ref(v_a_1827_);
v___x_1992_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_a_1827_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2136_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2136_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2136_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
if (lean_obj_tag(v_a_1993_) == 1)
{
lean_object* v_val_1997_; lean_object* v_fst_1998_; lean_object* v_snd_1999_; lean_object* v___x_2000_; 
lean_del_object(v___x_1995_);
v_val_1997_ = lean_ctor_get(v_a_1993_, 0);
lean_inc(v_val_1997_);
lean_dec_ref_known(v_a_1993_, 1);
v_fst_1998_ = lean_ctor_get(v_val_1997_, 0);
lean_inc(v_fst_1998_);
v_snd_1999_ = lean_ctor_get(v_val_1997_, 1);
lean_inc(v_snd_1999_);
lean_dec(v_val_1997_);
lean_inc_ref(v_b_1828_);
v___x_2000_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_b_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2123_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2123_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2123_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
if (lean_obj_tag(v_a_2001_) == 1)
{
lean_object* v_val_2005_; lean_object* v_fst_2006_; lean_object* v_snd_2007_; lean_object* v___x_2008_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; uint8_t v___x_2091_; 
lean_del_object(v___x_2003_);
v_val_2005_ = lean_ctor_get(v_a_2001_, 0);
lean_inc(v_val_2005_);
lean_dec_ref_known(v_a_2001_, 1);
v_fst_2006_ = lean_ctor_get(v_val_2005_, 0);
lean_inc(v_fst_2006_);
v_snd_2007_ = lean_ctor_get(v_val_2005_, 1);
lean_inc(v_snd_2007_);
lean_dec(v_val_2005_);
v___x_2008_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_nat_dec_eq(v_snd_1999_, v___x_2008_);
if (v___x_2091_ == 0)
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_nat_dec_eq(v_snd_2007_, v___x_2008_);
if (v___x_2092_ == 0)
{
uint8_t v___x_2093_; 
lean_dec_ref(v_b_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_eqFVarId_1823_);
v___x_2093_ = lean_nat_dec_lt(v_snd_1999_, v_snd_2007_);
if (v___x_2093_ == 0)
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_nat_dec_eq(v_snd_1999_, v_snd_2007_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = lean_nat_sub(v_snd_1999_, v_snd_2007_);
lean_dec(v_snd_1999_);
v___x_2096_ = l_Lean_mkNatLit(v___x_2095_);
v___x_2097_ = l_Lean_Meta_mkAdd(v_fst_1998_, v___x_2096_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v_fst_1877_ = v_a_2098_;
v_fst_1878_ = v_fst_2006_;
v_snd_1879_ = v_snd_2007_;
v___y_1880_ = v___y_1829_;
v___y_1881_ = v___y_1830_;
v___y_1882_ = v___y_1831_;
v___y_1883_ = v___y_1832_;
goto v___jp_1876_;
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_mvarId_1822_);
v_a_2099_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2097_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2097_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_dec(v_snd_2007_);
v_fst_1877_ = v_fst_1998_;
v_fst_1878_ = v_fst_2006_;
v_snd_1879_ = v_snd_1999_;
v___y_1880_ = v___y_1829_;
v___y_1881_ = v___y_1830_;
v___y_1882_ = v___y_1831_;
v___y_1883_ = v___y_1832_;
goto v___jp_1876_;
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_nat_sub(v_snd_2007_, v_snd_1999_);
lean_dec(v_snd_2007_);
v___x_2108_ = l_Lean_mkNatLit(v___x_2107_);
v___x_2109_ = l_Lean_Meta_mkAdd(v_fst_2006_, v___x_2108_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2109_, 1);
v_fst_1877_ = v_fst_1998_;
v_fst_1878_ = v_a_2110_;
v_snd_1879_ = v_snd_1999_;
v___y_1880_ = v___y_1829_;
v___y_1881_ = v___y_1830_;
v___y_1882_ = v___y_1831_;
v___y_1883_ = v___y_1832_;
goto v___jp_1876_;
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_snd_1999_);
lean_dec(v_fst_1998_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_mvarId_1822_);
v_a_2111_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2109_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2109_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
else
{
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
goto v___jp_2044_;
}
}
else
{
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
goto v___jp_2044_;
}
v___jp_2009_:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_nat_dec_lt(v___x_2008_, v_snd_2007_);
if (v___x_2013_ == 0)
{
lean_dec(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
goto v___jp_1870_;
}
else
{
lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__3));
v___x_2015_ = l_instBEqOption_beq___at___00Lean_Meta_unifyEq_x3f_spec__0(v___y_2010_, v___x_2014_);
lean_dec(v___y_2010_);
if (v___x_2015_ == 0)
{
lean_dec(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
goto v___jp_1870_;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2016_ = lean_unsigned_to_nat(1u);
v___x_2017_ = lean_nat_sub(v_snd_2007_, v___x_2016_);
lean_dec(v_snd_2007_);
v___x_2018_ = l_Lean_mkNatLit(v___x_2017_);
v___x_2019_ = l_Lean_Meta_mkAdd(v_fst_2006_, v___x_2018_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = lean_box(0);
v___x_2022_ = l_Lean_mkConst(v___y_2011_, v___x_2021_);
v___x_2023_ = l_Lean_Expr_app___override(v___x_2022_, v_a_2020_);
v___x_2024_ = lean_mk_empty_array_with_capacity(v___x_2016_);
v___x_2025_ = lean_array_push(v___x_2024_, v___x_2023_);
v___x_2026_ = l_Lean_Meta_mkAppM(v___y_2012_, v___x_2025_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v_hne_1835_ = v_a_2027_;
goto v___jp_1834_;
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v_a_2028_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v_a_2036_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2019_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2019_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
v___jp_2044_:
{
lean_object* v___x_2045_; lean_object* v_env_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2045_ = lean_st_ref_get(v___y_1832_);
v_env_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_ref(v_env_2046_);
lean_dec(v___x_2045_);
v___x_2047_ = lean_st_ref_get(v___y_1832_);
v___x_2048_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__5));
v___x_2049_ = l_Lean_Environment_contains(v_env_2046_, v___x_2048_, v___x_1824_);
if (v___x_2049_ == 0)
{
lean_dec(v___x_2047_);
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
lean_dec(v_snd_1999_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_b_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
goto v___jp_1867_;
}
else
{
lean_object* v_env_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v_env_2050_ = lean_ctor_get(v___x_2047_, 0);
lean_inc_ref(v_env_2050_);
lean_dec(v___x_2047_);
v___x_2051_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__8));
v___x_2052_ = l_Lean_Environment_contains(v_env_2050_, v___x_2051_, v___x_1824_);
if (v___x_2052_ == 0)
{
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
lean_dec(v_snd_1999_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_b_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
goto v___jp_1867_;
}
else
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_Meta_evalNat(v_b_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2055_ = l_Lean_Meta_evalNat(v_a_1827_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; uint8_t v___x_2057_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = lean_nat_dec_lt(v___x_2008_, v_snd_1999_);
if (v___x_2057_ == 0)
{
lean_dec(v_a_2054_);
lean_dec(v_snd_1999_);
lean_dec(v_fst_1998_);
v___y_2010_ = v_a_2056_;
v___y_2011_ = v___x_2048_;
v___y_2012_ = v___x_2051_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__3));
v___x_2059_ = l_instBEqOption_beq___at___00Lean_Meta_unifyEq_x3f_spec__0(v_a_2054_, v___x_2058_);
lean_dec(v_a_2054_);
if (v___x_2059_ == 0)
{
lean_dec(v_snd_1999_);
lean_dec(v_fst_1998_);
v___y_2010_ = v_a_2056_;
v___y_2011_ = v___x_2048_;
v___y_2012_ = v___x_2051_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec(v_a_2056_);
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
v___x_2060_ = lean_unsigned_to_nat(1u);
v___x_2061_ = lean_nat_sub(v_snd_1999_, v___x_2060_);
lean_dec(v_snd_1999_);
v___x_2062_ = l_Lean_mkNatLit(v___x_2061_);
v___x_2063_ = l_Lean_Meta_mkAdd(v_fst_1998_, v___x_2062_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2065_ = lean_obj_once(&l_Lean_Meta_unifyEq_x3f___lam__0___closed__9, &l_Lean_Meta_unifyEq_x3f___lam__0___closed__9_once, _init_l_Lean_Meta_unifyEq_x3f___lam__0___closed__9);
v___x_2066_ = l_Lean_Expr_app___override(v___x_2065_, v_a_2064_);
v_hne_1835_ = v___x_2066_;
goto v___jp_1834_;
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v_a_2067_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2063_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2063_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_2054_);
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
lean_dec(v_snd_1999_);
lean_dec(v_fst_1998_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v_a_2075_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2055_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2055_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
lean_dec(v_snd_1999_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_a_1827_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v_a_2083_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2053_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2053_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
lean_dec(v_a_2001_);
lean_dec(v_snd_1999_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_b_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v___x_2119_ = lean_box(0);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2119_);
v___x_2121_ = v___x_2003_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v_snd_1999_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_b_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v_a_2124_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2000_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2000_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
lean_dec(v_a_1993_);
lean_dec_ref(v_b_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v___x_2132_ = lean_box(0);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2132_);
v___x_2134_ = v___x_1995_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v_b_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v_a_2137_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_1992_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_1992_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
v___jp_1834_:
{
lean_object* v___x_1836_; 
lean_inc(v_mvarId_1822_);
v___x_1836_ = l_Lean_MVarId_getType(v_mvarId_1822_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = l_Lean_mkFVar(v_eqFVarId_1823_);
v___x_1839_ = l_Lean_Meta_mkAbsurd(v_a_1837_, v___x_1838_, v_hne_1835_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1849_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v___x_1841_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___redArg(v_mvarId_1822_, v_a_1840_, v___y_1830_);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v___x_1841_, 0);
lean_dec(v_unused_1850_);
v___x_1843_ = v___x_1841_;
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v___x_1841_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1845_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__0));
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1845_);
v___x_1847_ = v___x_1843_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_mvarId_1822_);
v_a_1851_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1839_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1839_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v_hne_1835_);
lean_dec(v_eqFVarId_1823_);
lean_dec(v_mvarId_1822_);
v_a_1859_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1836_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1836_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
v___jp_1867_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_box(0);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
v___jp_1870_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
v___jp_1876_:
{
lean_object* v___x_1884_; 
lean_inc(v_mvarId_1822_);
v___x_1884_ = l_Lean_MVarId_getType(v_mvarId_1822_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1886_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc_n(v_a_1885_, 2);
lean_dec_ref_known(v___x_1884_, 1);
v___x_1886_ = l_Lean_Meta_getLevel(v_a_1885_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1888_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
lean_inc_ref(v_fst_1878_);
lean_inc_ref(v_fst_1877_);
v___x_1888_ = l_Lean_Meta_mkEq(v_fst_1877_, v_fst_1878_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
lean_inc(v_a_1885_);
v___x_1890_ = l_Lean_mkArrow(v_a_1889_, v_a_1885_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1892_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
lean_inc(v_mvarId_1822_);
v___x_1892_ = l_Lean_MVarId_getTag(v_mvarId_1822_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v___x_1894_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1891_, v_a_1893_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1939_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc_n(v_a_1895_, 2);
lean_dec_ref_known(v___x_1894_, 1);
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1897_, 0, v_a_1887_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = l_Lean_mkConst(v___x_1875_, v___x_1897_);
v___x_1899_ = l_Lean_mkNatLit(v_snd_1879_);
lean_inc_ref(v_a_1825_);
v___x_1900_ = l_Lean_LocalDecl_toExpr(v_a_1825_);
v___x_1901_ = lean_unsigned_to_nat(6u);
v___x_1902_ = lean_mk_empty_array_with_capacity(v___x_1901_);
v___x_1903_ = lean_array_push(v___x_1902_, v_a_1885_);
v___x_1904_ = lean_array_push(v___x_1903_, v_fst_1877_);
v___x_1905_ = lean_array_push(v___x_1904_, v_fst_1878_);
v___x_1906_ = lean_array_push(v___x_1905_, v___x_1899_);
v___x_1907_ = lean_array_push(v___x_1906_, v___x_1900_);
v___x_1908_ = lean_array_push(v___x_1907_, v_a_1895_);
v___x_1909_ = l_Lean_mkAppN(v___x_1898_, v___x_1908_);
lean_dec_ref(v___x_1908_);
v___x_1910_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_spec__0___redArg(v_mvarId_1822_, v___x_1909_, v___y_1881_);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1910_, 0);
lean_dec(v_unused_1940_);
v___x_1912_ = v___x_1910_;
v_isShared_1913_ = v_isSharedCheck_1939_;
goto v_resetjp_1911_;
}
else
{
lean_dec(v___x_1910_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1939_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = l_Lean_Expr_mvarId_x21(v_a_1895_);
lean_dec(v_a_1895_);
v___x_1915_ = l_Lean_LocalDecl_fvarId(v_a_1825_);
lean_dec_ref(v_a_1825_);
v___x_1916_ = l_Lean_MVarId_tryClear(v___x_1914_, v___x_1915_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1930_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1930_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1930_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1921_ = lean_unsigned_to_nat(1u);
v___x_1922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1917_);
lean_ctor_set(v___x_1922_, 1, v_subst_1826_);
lean_ctor_set(v___x_1922_, 2, v___x_1921_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set_tag(v___x_1912_, 1);
lean_ctor_set(v___x_1912_, 0, v___x_1922_);
v___x_1924_ = v___x_1912_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1925_);
v___x_1927_ = v___x_1919_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_del_object(v___x_1912_);
lean_dec(v_subst_1826_);
v_a_1931_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1916_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1916_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_a_1887_);
lean_dec(v_a_1885_);
lean_dec(v_snd_1879_);
lean_dec_ref(v_fst_1878_);
lean_dec_ref(v_fst_1877_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_mvarId_1822_);
v_a_1941_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1894_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1894_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_a_1891_);
lean_dec(v_a_1887_);
lean_dec(v_a_1885_);
lean_dec(v_snd_1879_);
lean_dec_ref(v_fst_1878_);
lean_dec_ref(v_fst_1877_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_mvarId_1822_);
v_a_1949_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1892_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1892_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v_a_1887_);
lean_dec(v_a_1885_);
lean_dec(v_snd_1879_);
lean_dec_ref(v_fst_1878_);
lean_dec_ref(v_fst_1877_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_mvarId_1822_);
v_a_1957_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1890_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1890_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec(v_a_1887_);
lean_dec(v_a_1885_);
lean_dec(v_snd_1879_);
lean_dec_ref(v_fst_1878_);
lean_dec_ref(v_fst_1877_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_mvarId_1822_);
v_a_1965_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1888_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1888_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec(v_a_1885_);
lean_dec(v_snd_1879_);
lean_dec_ref(v_fst_1878_);
lean_dec_ref(v_fst_1877_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_mvarId_1822_);
v_a_1973_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1886_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1886_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
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
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_snd_1879_);
lean_dec_ref(v_fst_1878_);
lean_dec_ref(v_fst_1877_);
lean_dec(v_subst_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_mvarId_1822_);
v_a_1981_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1884_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1884_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___boxed(lean_object* v_mvarId_2145_, lean_object* v_eqFVarId_2146_, lean_object* v___x_2147_, lean_object* v_a_2148_, lean_object* v_subst_2149_, lean_object* v_a_2150_, lean_object* v_b_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v___x_11352__boxed_2157_; lean_object* v_res_2158_; 
v___x_11352__boxed_2157_ = lean_unbox(v___x_2147_);
v_res_2158_ = l_Lean_Meta_unifyEq_x3f___lam__0(v_mvarId_2145_, v_eqFVarId_2146_, v___x_11352__boxed_2157_, v_a_2148_, v_subst_2149_, v_a_2150_, v_b_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2158_;
}
}
static lean_object* _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__1___closed__1));
v___x_2163_ = l_Lean_stringToMessageData(v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1(lean_object* v_eqFVarId_2164_, lean_object* v_mvarId_2165_, lean_object* v_subst_2166_, lean_object* v_acyclic_2167_, lean_object* v_caseName_x3f_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2174_; 
lean_inc(v_eqFVarId_2164_);
v___x_2174_ = l_Lean_FVarId_getDecl___redArg(v_eqFVarId_2164_, v___y_2169_, v___y_2171_, v___y_2172_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2176_ = l_Lean_LocalDecl_type(v_a_2175_);
v___x_2177_ = l_Lean_Expr_isHEq(v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2178_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__1___closed__0));
v___x_2179_ = lean_unsigned_to_nat(3u);
v___x_2180_ = l_Lean_Expr_isAppOfArity(v___x_2176_, v___x_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec(v_a_2175_);
lean_dec(v_caseName_x3f_2168_);
lean_dec_ref(v_acyclic_2167_);
lean_dec(v_subst_2166_);
lean_dec(v_mvarId_2165_);
lean_dec(v_eqFVarId_2164_);
v___x_2181_ = lean_obj_once(&l_Lean_Meta_unifyEq_x3f___lam__1___closed__2, &l_Lean_Meta_unifyEq_x3f___lam__1___closed__2_once, _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__2);
v___x_2182_ = l_Lean_indentExpr(v___x_2176_);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_2183_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
return v___x_2184_;
}
else
{
lean_object* v___x_2185_; lean_object* v___f_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v_a_2191_; lean_object* v___x_2192_; 
v___x_2185_ = lean_box(v___x_2180_);
lean_inc(v_subst_2166_);
lean_inc(v_a_2175_);
lean_inc(v_eqFVarId_2164_);
lean_inc(v_mvarId_2165_);
v___f_2186_ = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2186_, 0, v_mvarId_2165_);
lean_closure_set(v___f_2186_, 1, v_eqFVarId_2164_);
lean_closure_set(v___f_2186_, 2, v___x_2185_);
lean_closure_set(v___f_2186_, 3, v_a_2175_);
lean_closure_set(v___f_2186_, 4, v_subst_2166_);
v___x_2187_ = l_Lean_Expr_appFn_x21(v___x_2176_);
v___x_2188_ = l_Lean_Expr_appArg_x21(v___x_2187_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = l_Lean_Expr_appArg_x21(v___x_2176_);
lean_dec_ref(v___x_2176_);
lean_inc_ref(v___x_2188_);
v___x_2190_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v___x_2188_, v___y_2170_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2190_);
lean_inc_ref(v___x_2189_);
v___x_2192_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v___x_2189_, v___y_2170_);
if (lean_obj_tag(v_a_2191_) == 1)
{
lean_object* v_a_2193_; 
lean_dec_ref(v___f_2186_);
lean_dec(v_caseName_x3f_2168_);
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref(v___x_2192_);
if (lean_obj_tag(v_a_2193_) == 1)
{
lean_object* v_fvarId_2194_; lean_object* v_fvarId_2195_; lean_object* v___x_2196_; 
v_fvarId_2194_ = lean_ctor_get(v_a_2191_, 0);
lean_inc(v_fvarId_2194_);
lean_dec_ref_known(v_a_2191_, 1);
v_fvarId_2195_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_fvarId_2195_);
lean_dec_ref_known(v_a_2193_, 1);
v___x_2196_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2194_, v___y_2169_, v___y_2171_, v___y_2172_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2198_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2195_, v___y_2169_, v___y_2171_, v___y_2172_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = l_Lean_LocalDecl_index(v_a_2197_);
lean_dec(v_a_2197_);
v___x_2201_ = l_Lean_LocalDecl_index(v_a_2199_);
lean_dec(v_a_2199_);
v___x_2202_ = lean_nat_dec_lt(v___x_2200_, v___x_2201_);
lean_dec(v___x_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_2165_, v_eqFVarId_2164_, v_subst_2166_, v_acyclic_2167_, v_a_2175_, v___x_2188_, v___x_2189_, v___x_2202_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v_a_2175_);
return v___x_2203_;
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_a_2197_);
lean_dec_ref(v___x_2189_);
lean_dec_ref(v___x_2188_);
lean_dec(v_a_2175_);
lean_dec_ref(v_acyclic_2167_);
lean_dec(v_subst_2166_);
lean_dec(v_mvarId_2165_);
lean_dec(v_eqFVarId_2164_);
v_a_2204_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2198_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2198_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_fvarId_2195_);
lean_dec_ref(v___x_2189_);
lean_dec_ref(v___x_2188_);
lean_dec(v_a_2175_);
lean_dec_ref(v_acyclic_2167_);
lean_dec(v_subst_2166_);
lean_dec(v_mvarId_2165_);
lean_dec(v_eqFVarId_2164_);
v_a_2212_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2196_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2196_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v___x_2220_; 
lean_dec_ref_known(v_a_2191_, 1);
lean_dec(v_a_2193_);
v___x_2220_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_2165_, v_eqFVarId_2164_, v_subst_2166_, v_acyclic_2167_, v_a_2175_, v___x_2188_, v___x_2189_, v___x_2177_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v_a_2175_);
return v___x_2220_;
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2260_; 
v_a_2221_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2223_ = v___x_2192_;
v_isShared_2224_ = v_isSharedCheck_2260_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2192_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2260_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
if (lean_obj_tag(v_a_2221_) == 1)
{
lean_object* v___x_2225_; 
lean_dec_ref_known(v_a_2221_, 1);
lean_del_object(v___x_2223_);
lean_dec(v_a_2191_);
lean_dec_ref(v___f_2186_);
lean_dec(v_caseName_x3f_2168_);
v___x_2225_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_2165_, v_eqFVarId_2164_, v_subst_2166_, v_acyclic_2167_, v_a_2175_, v___x_2188_, v___x_2189_, v___x_2180_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v_a_2175_);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; 
lean_dec_ref(v___x_2189_);
lean_dec_ref(v___x_2188_);
lean_dec_ref(v_acyclic_2167_);
lean_inc(v_a_2221_);
lean_inc(v_a_2191_);
v___x_2226_ = l_Lean_Meta_isExprDefEq(v_a_2191_, v_a_2221_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; uint8_t v___x_2228_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = lean_unbox(v_a_2227_);
lean_dec(v_a_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
lean_del_object(v___x_2223_);
v___x_2229_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_2165_, v_eqFVarId_2164_, v_subst_2166_, v_caseName_x3f_2168_, v_a_2175_, v___f_2186_, v_a_2191_, v_a_2221_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v_a_2175_);
return v___x_2229_;
}
else
{
lean_object* v___x_2230_; 
lean_dec(v_a_2221_);
lean_dec(v_a_2191_);
lean_dec_ref(v___f_2186_);
lean_dec(v_a_2175_);
lean_dec(v_caseName_x3f_2168_);
v___x_2230_ = l_Lean_MVarId_clear(v_mvarId_2165_, v_eqFVarId_2164_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2243_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2243_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2243_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2236_, 0, v_a_2231_);
lean_ctor_set(v___x_2236_, 1, v_subst_2166_);
lean_ctor_set(v___x_2236_, 2, v___x_2235_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 1);
lean_ctor_set(v___x_2223_, 0, v___x_2236_);
v___x_2238_ = v___x_2223_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2240_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2238_);
v___x_2240_ = v___x_2233_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_del_object(v___x_2223_);
lean_dec(v_subst_2166_);
v_a_2244_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2230_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2230_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_del_object(v___x_2223_);
lean_dec(v_a_2221_);
lean_dec(v_a_2191_);
lean_dec_ref(v___f_2186_);
lean_dec(v_a_2175_);
lean_dec(v_caseName_x3f_2168_);
lean_dec(v_subst_2166_);
lean_dec(v_mvarId_2165_);
lean_dec(v_eqFVarId_2164_);
v_a_2252_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2226_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2226_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
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
lean_object* v___x_2261_; 
lean_dec_ref(v___x_2176_);
lean_dec(v_caseName_x3f_2168_);
lean_dec_ref(v_acyclic_2167_);
lean_dec(v_eqFVarId_2164_);
v___x_2261_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(v_mvarId_2165_, v_a_2175_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v_a_2175_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2272_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2272_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2272_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2266_ = lean_unsigned_to_nat(1u);
v___x_2267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2267_, 0, v_a_2262_);
lean_ctor_set(v___x_2267_, 1, v_subst_2166_);
lean_ctor_set(v___x_2267_, 2, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2268_);
v___x_2270_ = v___x_2264_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec(v_subst_2166_);
v_a_2273_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2261_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2261_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v_caseName_x3f_2168_);
lean_dec_ref(v_acyclic_2167_);
lean_dec(v_subst_2166_);
lean_dec(v_mvarId_2165_);
lean_dec(v_eqFVarId_2164_);
v_a_2281_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2174_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2174_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___boxed(lean_object* v_eqFVarId_2289_, lean_object* v_mvarId_2290_, lean_object* v_subst_2291_, lean_object* v_acyclic_2292_, lean_object* v_caseName_x3f_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Meta_unifyEq_x3f___lam__1(v_eqFVarId_2289_, v_mvarId_2290_, v_subst_2291_, v_acyclic_2292_, v_caseName_x3f_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f(lean_object* v_mvarId_2300_, lean_object* v_eqFVarId_2301_, lean_object* v_subst_2302_, lean_object* v_acyclic_2303_, lean_object* v_caseName_x3f_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___f_2310_; lean_object* v___x_2311_; 
lean_inc(v_mvarId_2300_);
v___f_2310_ = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__1___boxed), 10, 5);
lean_closure_set(v___f_2310_, 0, v_eqFVarId_2301_);
lean_closure_set(v___f_2310_, 1, v_mvarId_2300_);
lean_closure_set(v___f_2310_, 2, v_subst_2302_);
lean_closure_set(v___f_2310_, 3, v_acyclic_2303_);
lean_closure_set(v___f_2310_, 4, v_caseName_x3f_2304_);
v___x_2311_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_2300_, v___f_2310_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___boxed(lean_object* v_mvarId_2312_, lean_object* v_eqFVarId_2313_, lean_object* v_subst_2314_, lean_object* v_acyclic_2315_, lean_object* v_caseName_x3f_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Meta_unifyEq_x3f(v_mvarId_2312_, v_eqFVarId_2313_, v_subst_2314_, v_acyclic_2315_, v_caseName_x3f_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
return v_res_2322_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_StringLitProof(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_StringLitProof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_StringLitProof(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_StringLitProof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_UnifyEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_UnifyEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_UnifyEq(builtin);
}
#ifdef __cplusplus
}
#endif
