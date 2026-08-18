// Lean compiler output
// Module: Lean.Meta.Tactic.Util
// Imports: public import Lean.Util.ForEachExprWhere public import Lean.Meta.PPGoal import Lean.Meta.AppBuilder
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_MetavarContext_setMVarUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_MVarId_setType___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "terminalTacticsAsSorry"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 90, 215, 151, 242, 202, 226, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 139, .m_capacity = 139, .m_length = 138, .m_data = "when enabled, terminal tactics such as `grind` and `omega` are replaced with `sorry`. Useful for debugging and fixing bootstrapping issues"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 233, 55, 94, 186, 188, 252, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 217, 134, 189, 91, 246, 107, 44)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_debug_terminalTacticsAsSorry;
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkTacticExMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Tactic `"};
static const lean_object* l_Lean_Meta_mkTacticExMsg___closed__0 = (const lean_object*)&l_Lean_Meta_mkTacticExMsg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkTacticExMsg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkTacticExMsg___closed__1;
static const lean_string_object l_Lean_Meta_mkTacticExMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` failed: "};
static const lean_object* l_Lean_Meta_mkTacticExMsg___closed__2 = (const lean_object*)&l_Lean_Meta_mkTacticExMsg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkTacticExMsg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkTacticExMsg___closed__3;
static const lean_string_object l_Lean_Meta_mkTacticExMsg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_Lean_Meta_mkTacticExMsg___closed__4 = (const lean_object*)&l_Lean_Meta_mkTacticExMsg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkTacticExMsg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkTacticExMsg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkTacticExMsg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_throwTacticEx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` failed\n\n"};
static const lean_object* l_Lean_Meta_throwTacticEx___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_throwTacticEx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_throwTacticEx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwTacticEx___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_throwNestedTacticEx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` failed with a nested error:\n"};
static const lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__1;
static const lean_string_object l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nested"};
static const lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_throwNestedTacticEx___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 50, 115, 245, 92, 68, 45, 137)}};
static const lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_checkNotAssigned___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "The metavariable below has already been assigned"};
static const lean_object* l_Lean_MVarId_checkNotAssigned___closed__0 = (const lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__1;
static const lean_string_object l_Lean_MVarId_checkNotAssigned___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "This likely indicates an internal error in this tactic or a prior one"};
static const lean_object* l_Lean_MVarId_checkNotAssigned___closed__2 = (const lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_checkNotAssigned___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__2_value)}};
static const lean_object* l_Lean_MVarId_checkNotAssigned___closed__3 = (const lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__3_value;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__4;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__5;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__6;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__7;
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 80, 134, 96, 135, 241, 87, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(12, 105, 212, 82, 205, 98, 36, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(141, 108, 151, 68, 40, 185, 49, 39)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 35, 20, 40, 241, 13, 114, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 161, 8, 73, 13, 24, 41, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 240, 21, 38, 82, 97, 50, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(240, 251, 182, 143, 63, 208, 115, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(124, 226, 182, 237, 212, 141, 147, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 251, 116, 130, 175, 2, 54, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 96, 175, 63, 15, 15, 160, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1901113268) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(57, 118, 41, 237, 158, 247, 69, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(170, 149, 39, 205, 173, 64, 129, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 101, 131, 162, 224, 178, 204, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(23, 46, 117, 252, 169, 255, 192, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_admit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "admit"};
static const lean_object* l_Lean_MVarId_admit___closed__0 = (const lean_object*)&l_Lean_MVarId_admit___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_admit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_admit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 138, 207, 107, 141, 184, 85, 68)}};
static const lean_object* l_Lean_MVarId_admit___closed__1 = (const lean_object*)&l_Lean_MVarId_admit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isFVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0 = (const lean_object*)&l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MVarId_getNondepPropHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_getNondepPropHyps___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_getNondepPropHyps___closed__0 = (const lean_object*)&l_Lean_MVarId_getNondepPropHyps___closed__0_value;
static const lean_closure_object l_Lean_MVarId_getNondepPropHyps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_getNondepPropHyps___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_getNondepPropHyps___closed__1 = (const lean_object*)&l_Lean_MVarId_getNondepPropHyps___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_inferInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "`infer_instance` tactic failed to assign instance"};
static const lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_inferInstance___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_inferInstance___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_inferInstance___lam__0___closed__0_value)}};
static const lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_inferInstance___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_inferInstance___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__2;
static lean_once_cell_t l_Lean_MVarId_inferInstance___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_inferInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "infer_instance"};
static const lean_object* l_Lean_MVarId_inferInstance___closed__0 = (const lean_object*)&l_Lean_MVarId_inferInstance___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_inferInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_inferInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 181, 58, 140, 126, 222, 16, 71)}};
static const lean_object* l_Lean_MVarId_inferInstance___closed__1 = (const lean_object*)&l_Lean_MVarId_inferInstance___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_isSubsingleton___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Subsingleton"};
static const lean_object* l_Lean_MVarId_isSubsingleton___closed__0 = (const lean_object*)&l_Lean_MVarId_isSubsingleton___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_isSubsingleton___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_isSubsingleton___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 130, 42, 228, 248, 162, 23, 186)}};
static const lean_object* l_Lean_MVarId_isSubsingleton___closed__1 = (const lean_object*)&l_Lean_MVarId_isSubsingleton___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "skipAssignedInstances"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 172, 231, 36, 182, 217, 37, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 113, .m_capacity = 113, .m_length = 112, .m_data = "in the `rw` and `simp` tactics, if an instance implicit argument is assigned, do not try to synthesize instance."};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 82, 89, 96, 183, 68, 254, 125)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 5, 107, 131, 111, 226, 218, 126)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag(lean_object* v_mvarId_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_MVarId_getDecl(v_mvarId_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_74_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_74_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v_userName_70_; lean_object* v___x_72_; 
v_userName_70_ = lean_ctor_get(v_a_66_, 0);
lean_inc(v_userName_70_);
lean_dec(v_a_66_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v_userName_70_);
v___x_72_ = v___x_68_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_userName_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_a_75_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_65_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_65_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag___boxed(lean_object* v_mvarId_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_MVarId_getTag(v_mvarId_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg(lean_object* v_mvarId_90_, lean_object* v_tag_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; lean_object* v_mctx_95_; lean_object* v_cache_96_; lean_object* v_zetaDeltaFVarIds_97_; lean_object* v_postponed_98_; lean_object* v_diag_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_110_; 
v___x_94_ = lean_st_ref_take(v_a_92_);
v_mctx_95_ = lean_ctor_get(v___x_94_, 0);
v_cache_96_ = lean_ctor_get(v___x_94_, 1);
v_zetaDeltaFVarIds_97_ = lean_ctor_get(v___x_94_, 2);
v_postponed_98_ = lean_ctor_get(v___x_94_, 3);
v_diag_99_ = lean_ctor_get(v___x_94_, 4);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_110_ == 0)
{
v___x_101_ = v___x_94_;
v_isShared_102_ = v_isSharedCheck_110_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_diag_99_);
lean_inc(v_postponed_98_);
lean_inc(v_zetaDeltaFVarIds_97_);
lean_inc(v_cache_96_);
lean_inc(v_mctx_95_);
lean_dec(v___x_94_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_110_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = l_Lean_MetavarContext_setMVarUserName(v_mctx_95_, v_mvarId_90_, v_tag_91_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_cache_96_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v_zetaDeltaFVarIds_97_);
lean_ctor_set(v_reuseFailAlloc_109_, 3, v_postponed_98_);
lean_ctor_set(v_reuseFailAlloc_109_, 4, v_diag_99_);
v___x_105_ = v_reuseFailAlloc_109_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_st_ref_put(v_a_92_, v___x_105_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg___boxed(lean_object* v_mvarId_111_, lean_object* v_tag_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_MVarId_setTag___redArg(v_mvarId_111_, v_tag_112_, v_a_113_);
lean_dec(v_a_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag(lean_object* v_mvarId_116_, lean_object* v_tag_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_MVarId_setTag___redArg(v_mvarId_116_, v_tag_117_, v_a_119_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___boxed(lean_object* v_mvarId_124_, lean_object* v_tag_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_MVarId_setTag(v_mvarId_124_, v_tag_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0(lean_object* v_suffix_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = l_Lean_Name_eraseMacroScopes(v_suffix_132_);
v___x_135_ = l_Lean_Name_append(v_x_133_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0___boxed(lean_object* v_suffix_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_appendTag___lam__0(v_suffix_136_, v_x_137_);
lean_dec(v_suffix_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object* v_tag_139_, lean_object* v_suffix_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = l_Lean_Name_hasMacroScopes(v_tag_139_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_appendTag___lam__0(v_suffix_140_, v_tag_139_);
return v___x_142_;
}
else
{
lean_object* v_view_143_; lean_object* v_name_144_; lean_object* v_imported_145_; lean_object* v_ctx_146_; lean_object* v_scopes_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_156_; 
v_view_143_ = l_Lean_extractMacroScopes(v_tag_139_);
v_name_144_ = lean_ctor_get(v_view_143_, 0);
v_imported_145_ = lean_ctor_get(v_view_143_, 1);
v_ctx_146_ = lean_ctor_get(v_view_143_, 2);
v_scopes_147_ = lean_ctor_get(v_view_143_, 3);
v_isSharedCheck_156_ = !lean_is_exclusive(v_view_143_);
if (v_isSharedCheck_156_ == 0)
{
v___x_149_ = v_view_143_;
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_scopes_147_);
lean_inc(v_ctx_146_);
lean_inc(v_imported_145_);
lean_inc(v_name_144_);
lean_dec(v_view_143_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = l_Lean_Meta_appendTag___lam__0(v_suffix_140_, v_name_144_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_imported_145_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_ctx_146_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v_scopes_147_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_MacroScopesView_review(v___x_153_);
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___boxed(lean_object* v_tag_157_, lean_object* v_suffix_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Meta_appendTag(v_tag_157_, v_suffix_158_);
lean_dec(v_suffix_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix(lean_object* v_mvarId_160_, lean_object* v_suffix_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
lean_inc(v_mvarId_160_);
v___x_167_ = l_Lean_MVarId_getTag(v_mvarId_160_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_167_, 1);
v___x_169_ = l_Lean_Meta_appendTag(v_a_168_, v_suffix_161_);
v___x_170_ = l_Lean_MVarId_setTag___redArg(v_mvarId_160_, v___x_169_, v_a_163_);
return v___x_170_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v_mvarId_160_);
v_a_171_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_167_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_167_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix___boxed(lean_object* v_mvarId_179_, lean_object* v_suffix_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Meta_appendTagSuffix(v_mvarId_179_, v_suffix_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_suffix_180_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object* v_type_187_, lean_object* v_tag_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_type_187_);
v___x_195_ = 2;
v___x_196_ = l_Lean_Meta_mkFreshExprMVar(v___x_194_, v___x_195_, v_tag_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(lean_object* v_type_197_, lean_object* v_tag_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_197_, v_tag_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
return v_res_204_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__0));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__3(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__2));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__5(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__4));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkTacticExMsg(lean_object* v_tacticName_214_, lean_object* v_mvarId_215_, lean_object* v_msg_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_217_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_218_ = l_Lean_MessageData_ofName(v_tacticName_214_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__3, &l_Lean_Meta_mkTacticExMsg___closed__3_once, _init_l_Lean_Meta_mkTacticExMsg___closed__3);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_msg_216_);
v___x_223_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__5, &l_Lean_Meta_mkTacticExMsg___closed__5_once, _init_l_Lean_Meta_mkTacticExMsg___closed__5);
v___x_224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_mvarId_215_);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(lean_object* v_msgData_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; lean_object* v_env_234_; lean_object* v___x_235_; lean_object* v_mctx_236_; lean_object* v_lctx_237_; lean_object* v_options_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_233_ = lean_st_ref_get(v___y_231_);
v_env_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_env_234_);
lean_dec(v___x_233_);
v___x_235_ = lean_st_ref_get(v___y_229_);
v_mctx_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref(v_mctx_236_);
lean_dec(v___x_235_);
v_lctx_237_ = lean_ctor_get(v___y_228_, 2);
v_options_238_ = lean_ctor_get(v___y_230_, 2);
lean_inc_ref(v_options_238_);
lean_inc_ref(v_lctx_237_);
v___x_239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_239_, 0, v_env_234_);
lean_ctor_set(v___x_239_, 1, v_mctx_236_);
lean_ctor_set(v___x_239_, 2, v_lctx_237_);
lean_ctor_set(v___x_239_, 3, v_options_238_);
v___x_240_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v_msgData_227_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object* v_msgData_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_ref_255_; lean_object* v___x_256_; lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_ref_255_ = lean_ctor_get(v___y_252_, 5);
v___x_256_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_265_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
lean_inc(v_ref_255_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_ref_255_);
lean_ctor_set(v___x_261_, 1, v_a_257_);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 1);
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
static lean_object* _init_l_Lean_Meta_throwTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Meta_throwTacticEx___redArg___closed__0));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object* v_tacticName_276_, lean_object* v_mvarId_277_, lean_object* v_msg_x3f_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
if (lean_obj_tag(v_msg_x3f_278_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_284_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_285_ = l_Lean_MessageData_ofName(v_tacticName_276_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_obj_once(&l_Lean_Meta_throwTacticEx___redArg___closed__1, &l_Lean_Meta_throwTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwTacticEx___redArg___closed__1);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_mvarId_277_);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_290_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
return v___x_291_;
}
else
{
lean_object* v_val_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_val_292_ = lean_ctor_get(v_msg_x3f_278_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v_msg_x3f_278_, 1);
v___x_293_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_276_, v_mvarId_277_, v_val_292_);
v___x_294_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_293_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object* v_tacticName_295_, lean_object* v_mvarId_296_, lean_object* v_msg_x3f_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_295_, v_mvarId_296_, v_msg_x3f_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object* v_00_u03b1_304_, lean_object* v_tacticName_305_, lean_object* v_mvarId_306_, lean_object* v_msg_x3f_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_305_, v_mvarId_306_, v_msg_x3f_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object* v_00_u03b1_314_, lean_object* v_tacticName_315_, lean_object* v_mvarId_316_, lean_object* v_msg_x3f_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_throwTacticEx(v_00_u03b1_314_, v_tacticName_315_, v_mvarId_316_, v_msg_x3f_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object* v_00_u03b1_324_, lean_object* v_msg_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object* v_00_u03b1_332_, lean_object* v_msg_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(v_00_u03b1_332_, v_msg_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object* v_tacticName_346_, lean_object* v_ex_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_nestedMsg_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_msg_359_; lean_object* v_kind_360_; uint8_t v___x_361_; 
v_nestedMsg_353_ = l_Lean_Exception_toMessageData(v_ex_347_);
v___x_354_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_355_ = l_Lean_MessageData_ofName(v_tacticName_346_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_obj_once(&l_Lean_Meta_throwNestedTacticEx___redArg___closed__1, &l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
lean_inc_ref(v_nestedMsg_353_);
v_msg_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_359_, 0, v___x_358_);
lean_ctor_set(v_msg_359_, 1, v_nestedMsg_353_);
v_kind_360_ = l_Lean_MessageData_kind(v_nestedMsg_353_);
lean_dec_ref(v_nestedMsg_353_);
v___x_361_ = l_Lean_Name_isAnonymous(v_kind_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3));
v___x_363_ = l_Lean_Name_append(v___x_362_, v_kind_360_);
v___x_364_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_msg_359_);
v___x_365_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_364_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
lean_dec(v_kind_360_);
v___x_366_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_359_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object* v_tacticName_367_, lean_object* v_ex_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_367_, v_ex_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object* v_00_u03b1_375_, lean_object* v_tacticName_376_, lean_object* v_ex_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_376_, v_ex_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object* v_00_u03b1_384_, lean_object* v_tacticName_385_, lean_object* v_ex_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_throwNestedTacticEx(v_00_u03b1_384_, v_tacticName_385_, v_ex_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
return v_res_392_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_393_, lean_object* v_i_394_, lean_object* v_k_395_){
_start:
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_array_get_size(v_keys_393_);
v___x_397_ = lean_nat_dec_lt(v_i_394_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec(v_i_394_);
return v___x_397_;
}
else
{
lean_object* v_k_x27_398_; uint8_t v___x_399_; 
v_k_x27_398_ = lean_array_fget_borrowed(v_keys_393_, v_i_394_);
v___x_399_ = l_Lean_instBEqMVarId_beq(v_k_395_, v_k_x27_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_add(v_i_394_, v___x_400_);
lean_dec(v_i_394_);
v_i_394_ = v___x_401_;
goto _start;
}
else
{
lean_dec(v_i_394_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_403_, lean_object* v_i_404_, lean_object* v_k_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_403_, v_i_404_, v_k_405_);
lean_dec(v_k_405_);
lean_dec_ref(v_keys_403_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object* v_x_408_, size_t v_x_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
lean_object* v_es_411_; lean_object* v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v_j_415_; lean_object* v___x_416_; 
v_es_411_ = lean_ctor_get(v_x_408_, 0);
v___x_412_ = lean_box(2);
v___x_413_ = ((size_t)31ULL);
v___x_414_ = lean_usize_land(v_x_409_, v___x_413_);
v_j_415_ = lean_usize_to_nat(v___x_414_);
v___x_416_ = lean_array_get_borrowed(v___x_412_, v_es_411_, v_j_415_);
lean_dec(v_j_415_);
switch(lean_obj_tag(v___x_416_))
{
case 0:
{
lean_object* v_key_417_; uint8_t v___x_418_; 
v_key_417_ = lean_ctor_get(v___x_416_, 0);
v___x_418_ = l_Lean_instBEqMVarId_beq(v_x_410_, v_key_417_);
return v___x_418_;
}
case 1:
{
lean_object* v_node_419_; size_t v___x_420_; size_t v___x_421_; 
v_node_419_ = lean_ctor_get(v___x_416_, 0);
v___x_420_ = ((size_t)5ULL);
v___x_421_ = lean_usize_shift_right(v_x_409_, v___x_420_);
v_x_408_ = v_node_419_;
v_x_409_ = v___x_421_;
goto _start;
}
default: 
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
}
else
{
lean_object* v_ks_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_ks_424_ = lean_ctor_get(v_x_408_, 0);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_424_, v___x_425_, v_x_410_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
size_t v_x_580__boxed_430_; uint8_t v_res_431_; lean_object* v_r_432_; 
v_x_580__boxed_430_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_431_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_427_, v_x_580__boxed_430_, v_x_429_);
lean_dec(v_x_429_);
lean_dec_ref(v_x_427_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
uint64_t v___x_435_; size_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = l_Lean_instHashableMVarId_hash(v_x_434_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_433_, v___x_436_, v_x_434_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_438_, v_x_439_);
lean_dec(v_x_439_);
lean_dec_ref(v_x_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object* v_mvarId_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; lean_object* v_mctx_446_; lean_object* v_eAssignment_447_; uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_445_ = lean_st_ref_get(v___y_443_);
v_mctx_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc_ref(v_mctx_446_);
lean_dec(v___x_445_);
v_eAssignment_447_ = lean_ctor_get(v_mctx_446_, 8);
lean_inc_ref(v_eAssignment_447_);
lean_dec_ref(v_mctx_446_);
v___x_448_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_447_, v_mvarId_442_);
lean_dec_ref(v_eAssignment_447_);
v___x_449_ = lean_box(v___x_448_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object* v_mvarId_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec(v_mvarId_451_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__0));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__4(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__3));
v___x_462_ = l_Lean_MessageData_ofFormat(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__5(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__4, &l_Lean_MVarId_checkNotAssigned___closed__4_once, _init_l_Lean_MVarId_checkNotAssigned___closed__4);
v___x_464_ = l_Lean_MessageData_note(v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__6(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__5, &l_Lean_MVarId_checkNotAssigned___closed__5_once, _init_l_Lean_MVarId_checkNotAssigned___closed__5);
v___x_466_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__1, &l_Lean_MVarId_checkNotAssigned___closed__1_once, _init_l_Lean_MVarId_checkNotAssigned___closed__1);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__7(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__6, &l_Lean_MVarId_checkNotAssigned___closed__6_once, _init_l_Lean_MVarId_checkNotAssigned___closed__6);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object* v_mvarId_470_, lean_object* v_tacticName_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_489_; 
v___x_477_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_470_, v_a_473_);
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_489_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v___x_482_; 
v___x_482_ = lean_unbox(v_a_478_);
lean_dec(v_a_478_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v_tacticName_471_);
lean_dec(v_mvarId_470_);
v___x_483_ = lean_box(0);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_483_);
v___x_485_ = v___x_480_;
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
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_del_object(v___x_480_);
v___x_487_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__7, &l_Lean_MVarId_checkNotAssigned___closed__7_once, _init_l_Lean_MVarId_checkNotAssigned___closed__7);
v___x_488_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_471_, v_mvarId_470_, v___x_487_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object* v_mvarId_490_, lean_object* v_tacticName_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_490_, v_tacticName_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object* v_mvarId_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_498_, v___y_500_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object* v_mvarId_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(v_mvarId_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v_mvarId_505_);
return v_res_511_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object* v_00_u03b2_512_, lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_513_, v_x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_516_, v_x_517_, v_x_518_);
lean_dec(v_x_518_);
lean_dec_ref(v_x_517_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_521_, lean_object* v_x_522_, size_t v_x_523_, lean_object* v_x_524_){
_start:
{
uint8_t v___x_525_; 
v___x_525_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_522_, v_x_523_, v_x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_526_, lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
size_t v_x_747__boxed_530_; uint8_t v_res_531_; lean_object* v_r_532_; 
v_x_747__boxed_530_ = lean_unbox_usize(v_x_528_);
lean_dec(v_x_528_);
v_res_531_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_526_, v_x_527_, v_x_747__boxed_530_, v_x_529_);
lean_dec(v_x_529_);
lean_dec_ref(v_x_527_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_533_, lean_object* v_keys_534_, lean_object* v_vals_535_, lean_object* v_heq_536_, lean_object* v_i_537_, lean_object* v_k_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_534_, v_i_537_, v_k_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_540_, lean_object* v_keys_541_, lean_object* v_vals_542_, lean_object* v_heq_543_, lean_object* v_i_544_, lean_object* v_k_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_540_, v_keys_541_, v_vals_542_, v_heq_543_, v_i_544_, v_k_545_);
lean_dec(v_k_545_);
lean_dec_ref(v_vals_542_);
lean_dec_ref(v_keys_541_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object* v_mvarId_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_MVarId_getDecl(v_mvarId_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_type_559_; lean_object* v___x_561_; 
v_type_559_ = lean_ctor_get(v_a_555_, 2);
lean_inc_ref(v_type_559_);
lean_dec(v_a_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_type_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_type_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_564_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_554_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_554_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object* v_mvarId_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_MVarId_getType(v_mvarId_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object* v_e_579_, lean_object* v___y_580_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = l_Lean_Expr_hasMVar(v_e_579_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_e_579_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v_mctx_585_; lean_object* v___x_586_; lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_589_; lean_object* v_cache_590_; lean_object* v_zetaDeltaFVarIds_591_; lean_object* v_postponed_592_; lean_object* v_diag_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_602_; 
v___x_584_ = lean_st_ref_get(v___y_580_);
v_mctx_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc_ref(v_mctx_585_);
lean_dec(v___x_584_);
v___x_586_ = l_Lean_instantiateMVarsCore(v_mctx_585_, v_e_579_);
v_fst_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v___x_586_, 1);
lean_inc(v_snd_588_);
lean_dec_ref(v___x_586_);
v___x_589_ = lean_st_ref_take(v___y_580_);
v_cache_590_ = lean_ctor_get(v___x_589_, 1);
v_zetaDeltaFVarIds_591_ = lean_ctor_get(v___x_589_, 2);
v_postponed_592_ = lean_ctor_get(v___x_589_, 3);
v_diag_593_ = lean_ctor_get(v___x_589_, 4);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v___x_589_, 0);
lean_dec(v_unused_603_);
v___x_595_ = v___x_589_;
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_diag_593_);
lean_inc(v_postponed_592_);
lean_inc(v_zetaDeltaFVarIds_591_);
lean_inc(v_cache_590_);
lean_dec(v___x_589_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_snd_588_);
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_snd_588_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_cache_590_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_zetaDeltaFVarIds_591_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_postponed_592_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_diag_593_);
v___x_598_ = v_reuseFailAlloc_601_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_st_ref_put(v___y_580_, v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_fst_587_);
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object* v_e_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_604_, v___y_605_);
lean_dec(v___y_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object* v_e_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_608_, v___y_610_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object* v_e_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(v_e_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object* v_mvarId_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_MVarId_getType(v_mvarId_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
lean_inc(v_a_626_);
lean_inc_ref(v_a_625_);
lean_inc(v_a_624_);
lean_inc_ref(v_a_623_);
v___x_630_ = lean_whnf(v_a_629_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_631_, v_a_624_);
return v___x_632_;
}
else
{
return v___x_630_;
}
}
else
{
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object* v_mvarId_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_MVarId_getType_x27(v_mvarId_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_706_ = 0;
v___x_707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_708_ = l_Lean_registerTraceClass(v___x_705_, v___x_706_, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object* v_mvarId_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_711_, v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_718_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_718_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object* v_mvarId_735_, lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_735_, v_x_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object* v_00_u03b1_743_, lean_object* v_mvarId_744_, lean_object* v_x_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_744_, v_x_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object* v_00_u03b1_752_, lean_object* v_mvarId_753_, lean_object* v_x_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(v_00_u03b1_752_, v_mvarId_753_, v_x_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
lean_object* v_ks_765_; lean_object* v_vs_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_790_; 
v_ks_765_ = lean_ctor_get(v_x_761_, 0);
v_vs_766_ = lean_ctor_get(v_x_761_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_790_ == 0)
{
v___x_768_ = v_x_761_;
v_isShared_769_ = v_isSharedCheck_790_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_vs_766_);
lean_inc(v_ks_765_);
lean_dec(v_x_761_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_790_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_array_get_size(v_ks_765_);
v___x_771_ = lean_nat_dec_lt(v_x_762_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec(v_x_762_);
v___x_772_ = lean_array_push(v_ks_765_, v_x_763_);
v___x_773_ = lean_array_push(v_vs_766_, v_x_764_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_773_);
lean_ctor_set(v___x_768_, 0, v___x_772_);
v___x_775_ = v___x_768_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_773_);
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
lean_object* v_k_x27_777_; uint8_t v___x_778_; 
v_k_x27_777_ = lean_array_fget_borrowed(v_ks_765_, v_x_762_);
v___x_778_ = l_Lean_instBEqMVarId_beq(v_x_763_, v_k_x27_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_780_; 
if (v_isShared_769_ == 0)
{
v___x_780_ = v___x_768_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_ks_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_vs_766_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_x_762_, v___x_781_);
lean_dec(v_x_762_);
v_x_761_ = v___x_780_;
v_x_762_ = v___x_782_;
goto _start;
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = lean_array_fset(v_ks_765_, v_x_762_, v_x_763_);
v___x_786_ = lean_array_fset(v_vs_766_, v_x_762_, v_x_764_);
lean_dec(v_x_762_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_786_);
lean_ctor_set(v___x_768_, 0, v___x_785_);
v___x_788_ = v___x_768_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_791_, lean_object* v_k_792_, lean_object* v_v_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_791_, v___x_794_, v_k_792_, v_v_793_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object* v_x_797_, size_t v_x_798_, size_t v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
lean_object* v_es_802_; size_t v___x_803_; size_t v___x_804_; lean_object* v_j_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_es_802_ = lean_ctor_get(v_x_797_, 0);
v___x_803_ = ((size_t)31ULL);
v___x_804_ = lean_usize_land(v_x_798_, v___x_803_);
v_j_805_ = lean_usize_to_nat(v___x_804_);
v___x_806_ = lean_array_get_size(v_es_802_);
v___x_807_ = lean_nat_dec_lt(v_j_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_dec(v_j_805_);
lean_dec(v_x_801_);
lean_dec(v_x_800_);
return v_x_797_;
}
else
{
lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_846_; 
lean_inc_ref(v_es_802_);
v_isSharedCheck_846_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v_x_797_, 0);
lean_dec(v_unused_847_);
v___x_809_ = v_x_797_;
v_isShared_810_ = v_isSharedCheck_846_;
goto v_resetjp_808_;
}
else
{
lean_dec(v_x_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_846_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_v_811_; lean_object* v___x_812_; lean_object* v_xs_x27_813_; lean_object* v___y_815_; 
v_v_811_ = lean_array_fget(v_es_802_, v_j_805_);
v___x_812_ = lean_box(0);
v_xs_x27_813_ = lean_array_fset(v_es_802_, v_j_805_, v___x_812_);
switch(lean_obj_tag(v_v_811_))
{
case 0:
{
lean_object* v_key_820_; lean_object* v_val_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_831_; 
v_key_820_ = lean_ctor_get(v_v_811_, 0);
v_val_821_ = lean_ctor_get(v_v_811_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_v_811_);
if (v_isSharedCheck_831_ == 0)
{
v___x_823_ = v_v_811_;
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_val_821_);
lean_inc(v_key_820_);
lean_dec(v_v_811_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___x_825_; 
v___x_825_ = l_Lean_instBEqMVarId_beq(v_x_800_, v_key_820_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_del_object(v___x_823_);
v___x_826_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_820_, v_val_821_, v_x_800_, v_x_801_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___y_815_ = v___x_827_;
goto v___jp_814_;
}
else
{
lean_object* v___x_829_; 
lean_dec(v_val_821_);
lean_dec(v_key_820_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_x_801_);
lean_ctor_set(v___x_823_, 0, v_x_800_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_x_800_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_x_801_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
v___y_815_ = v___x_829_;
goto v___jp_814_;
}
}
}
}
case 1:
{
lean_object* v_node_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_844_; 
v_node_832_ = lean_ctor_get(v_v_811_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_v_811_);
if (v_isSharedCheck_844_ == 0)
{
v___x_834_ = v_v_811_;
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_node_832_);
lean_dec(v_v_811_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_836_ = ((size_t)5ULL);
v___x_837_ = lean_usize_shift_right(v_x_798_, v___x_836_);
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_add(v_x_799_, v___x_838_);
v___x_840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_832_, v___x_837_, v___x_839_, v_x_800_, v_x_801_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_840_);
v___x_842_ = v___x_834_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
v___y_815_ = v___x_842_;
goto v___jp_814_;
}
}
}
default: 
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_x_800_);
lean_ctor_set(v___x_845_, 1, v_x_801_);
v___y_815_ = v___x_845_;
goto v___jp_814_;
}
}
v___jp_814_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_array_fset(v_xs_x27_813_, v_j_805_, v___y_815_);
lean_dec(v_j_805_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_816_);
v___x_818_ = v___x_809_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
else
{
lean_object* v_ks_848_; lean_object* v_vs_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_869_; 
v_ks_848_ = lean_ctor_get(v_x_797_, 0);
v_vs_849_ = lean_ctor_get(v_x_797_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_869_ == 0)
{
v___x_851_ = v_x_797_;
v_isShared_852_ = v_isSharedCheck_869_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_vs_849_);
lean_inc(v_ks_848_);
lean_dec(v_x_797_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_869_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_ks_848_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_vs_849_);
v___x_854_ = v_reuseFailAlloc_868_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v_newNode_855_; uint8_t v___y_857_; size_t v___x_863_; uint8_t v___x_864_; 
v_newNode_855_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v___x_854_, v_x_800_, v_x_801_);
v___x_863_ = ((size_t)7ULL);
v___x_864_ = lean_usize_dec_le(v___x_863_, v_x_799_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_865_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_855_);
v___x_866_ = lean_unsigned_to_nat(4u);
v___x_867_ = lean_nat_dec_lt(v___x_865_, v___x_866_);
lean_dec(v___x_865_);
v___y_857_ = v___x_867_;
goto v___jp_856_;
}
else
{
v___y_857_ = v___x_864_;
goto v___jp_856_;
}
v___jp_856_:
{
if (v___y_857_ == 0)
{
lean_object* v_ks_858_; lean_object* v_vs_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_ks_858_ = lean_ctor_get(v_newNode_855_, 0);
lean_inc_ref(v_ks_858_);
v_vs_859_ = lean_ctor_get(v_newNode_855_, 1);
lean_inc_ref(v_vs_859_);
lean_dec_ref(v_newNode_855_);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_799_, v_ks_858_, v_vs_859_, v___x_860_, v___x_861_);
lean_dec_ref(v_vs_859_);
lean_dec_ref(v_ks_858_);
return v___x_862_;
}
else
{
return v_newNode_855_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_870_, lean_object* v_keys_871_, lean_object* v_vals_872_, lean_object* v_i_873_, lean_object* v_entries_874_){
_start:
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_array_get_size(v_keys_871_);
v___x_876_ = lean_nat_dec_lt(v_i_873_, v___x_875_);
if (v___x_876_ == 0)
{
lean_dec(v_i_873_);
return v_entries_874_;
}
else
{
lean_object* v_k_877_; lean_object* v_v_878_; uint64_t v___x_879_; size_t v_h_880_; size_t v___x_881_; lean_object* v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; size_t v_h_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_k_877_ = lean_array_fget_borrowed(v_keys_871_, v_i_873_);
v_v_878_ = lean_array_fget_borrowed(v_vals_872_, v_i_873_);
v___x_879_ = l_Lean_instHashableMVarId_hash(v_k_877_);
v_h_880_ = lean_uint64_to_usize(v___x_879_);
v___x_881_ = ((size_t)5ULL);
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = ((size_t)1ULL);
v___x_884_ = lean_usize_sub(v_depth_870_, v___x_883_);
v___x_885_ = lean_usize_mul(v___x_881_, v___x_884_);
v_h_886_ = lean_usize_shift_right(v_h_880_, v___x_885_);
v___x_887_ = lean_nat_add(v_i_873_, v___x_882_);
lean_dec(v_i_873_);
lean_inc(v_v_878_);
lean_inc(v_k_877_);
v___x_888_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_entries_874_, v_h_886_, v_depth_870_, v_k_877_, v_v_878_);
v_i_873_ = v___x_887_;
v_entries_874_ = v___x_888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_890_, lean_object* v_keys_891_, lean_object* v_vals_892_, lean_object* v_i_893_, lean_object* v_entries_894_){
_start:
{
size_t v_depth_boxed_895_; lean_object* v_res_896_; 
v_depth_boxed_895_ = lean_unbox_usize(v_depth_890_);
lean_dec(v_depth_890_);
v_res_896_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_895_, v_keys_891_, v_vals_892_, v_i_893_, v_entries_894_);
lean_dec_ref(v_vals_892_);
lean_dec_ref(v_keys_891_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
size_t v_x_1011__boxed_902_; size_t v_x_1012__boxed_903_; lean_object* v_res_904_; 
v_x_1011__boxed_902_ = lean_unbox_usize(v_x_898_);
lean_dec(v_x_898_);
v_x_1012__boxed_903_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_res_904_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_897_, v_x_1011__boxed_902_, v_x_1012__boxed_903_, v_x_900_, v_x_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
uint64_t v___x_908_; size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; 
v___x_908_ = l_Lean_instHashableMVarId_hash(v_x_906_);
v___x_909_ = lean_uint64_to_usize(v___x_908_);
v___x_910_ = ((size_t)1ULL);
v___x_911_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_905_, v___x_909_, v___x_910_, v_x_906_, v_x_907_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object* v_mvarId_912_, lean_object* v_val_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; lean_object* v_mctx_917_; lean_object* v_cache_918_; lean_object* v_zetaDeltaFVarIds_919_; lean_object* v_postponed_920_; lean_object* v_diag_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_950_; 
v___x_916_ = lean_st_ref_take(v___y_914_);
v_mctx_917_ = lean_ctor_get(v___x_916_, 0);
v_cache_918_ = lean_ctor_get(v___x_916_, 1);
v_zetaDeltaFVarIds_919_ = lean_ctor_get(v___x_916_, 2);
v_postponed_920_ = lean_ctor_get(v___x_916_, 3);
v_diag_921_ = lean_ctor_get(v___x_916_, 4);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_950_ == 0)
{
v___x_923_ = v___x_916_;
v_isShared_924_ = v_isSharedCheck_950_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_diag_921_);
lean_inc(v_postponed_920_);
lean_inc(v_zetaDeltaFVarIds_919_);
lean_inc(v_cache_918_);
lean_inc(v_mctx_917_);
lean_dec(v___x_916_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_950_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_depth_925_; lean_object* v_levelAssignDepth_926_; lean_object* v_lmvarCounter_927_; lean_object* v_mvarCounter_928_; lean_object* v_lDecls_929_; lean_object* v_decls_930_; lean_object* v_userNames_931_; lean_object* v_lAssignment_932_; lean_object* v_eAssignment_933_; lean_object* v_dAssignment_934_; lean_object* v_instanceTypedMVars_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_949_; 
v_depth_925_ = lean_ctor_get(v_mctx_917_, 0);
v_levelAssignDepth_926_ = lean_ctor_get(v_mctx_917_, 1);
v_lmvarCounter_927_ = lean_ctor_get(v_mctx_917_, 2);
v_mvarCounter_928_ = lean_ctor_get(v_mctx_917_, 3);
v_lDecls_929_ = lean_ctor_get(v_mctx_917_, 4);
v_decls_930_ = lean_ctor_get(v_mctx_917_, 5);
v_userNames_931_ = lean_ctor_get(v_mctx_917_, 6);
v_lAssignment_932_ = lean_ctor_get(v_mctx_917_, 7);
v_eAssignment_933_ = lean_ctor_get(v_mctx_917_, 8);
v_dAssignment_934_ = lean_ctor_get(v_mctx_917_, 9);
v_instanceTypedMVars_935_ = lean_ctor_get(v_mctx_917_, 10);
v_isSharedCheck_949_ = !lean_is_exclusive(v_mctx_917_);
if (v_isSharedCheck_949_ == 0)
{
v___x_937_ = v_mctx_917_;
v_isShared_938_ = v_isSharedCheck_949_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_instanceTypedMVars_935_);
lean_inc(v_dAssignment_934_);
lean_inc(v_eAssignment_933_);
lean_inc(v_lAssignment_932_);
lean_inc(v_userNames_931_);
lean_inc(v_decls_930_);
lean_inc(v_lDecls_929_);
lean_inc(v_mvarCounter_928_);
lean_inc(v_lmvarCounter_927_);
lean_inc(v_levelAssignDepth_926_);
lean_inc(v_depth_925_);
lean_dec(v_mctx_917_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_949_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_933_, v_mvarId_912_, v_val_913_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 8, v___x_939_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_depth_925_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_levelAssignDepth_926_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_lmvarCounter_927_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_mvarCounter_928_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_lDecls_929_);
lean_ctor_set(v_reuseFailAlloc_948_, 5, v_decls_930_);
lean_ctor_set(v_reuseFailAlloc_948_, 6, v_userNames_931_);
lean_ctor_set(v_reuseFailAlloc_948_, 7, v_lAssignment_932_);
lean_ctor_set(v_reuseFailAlloc_948_, 8, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_948_, 9, v_dAssignment_934_);
lean_ctor_set(v_reuseFailAlloc_948_, 10, v_instanceTypedMVars_935_);
v___x_941_ = v_reuseFailAlloc_948_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_941_);
v___x_943_ = v___x_923_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_cache_918_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_zetaDeltaFVarIds_919_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_postponed_920_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_diag_921_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_st_ref_put(v___y_914_, v___x_943_);
v___x_945_ = lean_box(0);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object* v_mvarId_951_, lean_object* v_val_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_951_, v_val_952_, v___y_953_);
lean_dec(v___y_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object* v_mvarId_956_, lean_object* v___x_957_, uint8_t v_synthetic_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
lean_inc(v_mvarId_956_);
v___x_964_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_956_, v___x_957_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v___x_965_; 
lean_dec_ref_known(v___x_964_, 1);
lean_inc(v_mvarId_956_);
v___x_965_ = l_Lean_MVarId_getType(v_mvarId_956_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; uint8_t v___x_967_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = 1;
v___x_968_ = l_Lean_Meta_mkLabeledSorry(v_a_966_, v_synthetic_958_, v___x_967_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_956_, v_a_969_, v___y_960_);
return v___x_970_;
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_mvarId_956_);
v_a_971_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_968_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_968_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v_mvarId_956_);
v_a_979_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_965_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_965_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
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
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_dec(v_mvarId_956_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object* v_mvarId_987_, lean_object* v___x_988_, lean_object* v_synthetic_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v_synthetic_boxed_995_; lean_object* v_res_996_; 
v_synthetic_boxed_995_ = lean_unbox(v_synthetic_989_);
v_res_996_ = l_Lean_MVarId_admit___lam__0(v_mvarId_987_, v___x_988_, v_synthetic_boxed_995_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object* v_mvarId_1000_, uint8_t v_synthetic_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; 
v___x_1007_ = ((lean_object*)(l_Lean_MVarId_admit___closed__1));
v___x_1008_ = lean_box(v_synthetic_1001_);
lean_inc(v_mvarId_1000_);
v___f_1009_ = lean_alloc_closure((void*)(l_Lean_MVarId_admit___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1009_, 0, v_mvarId_1000_);
lean_closure_set(v___f_1009_, 1, v___x_1007_);
lean_closure_set(v___f_1009_, 2, v___x_1008_);
v___x_1010_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_1000_, v___f_1009_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object* v_mvarId_1011_, lean_object* v_synthetic_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
uint8_t v_synthetic_boxed_1018_; lean_object* v_res_1019_; 
v_synthetic_boxed_1018_ = lean_unbox(v_synthetic_1012_);
v_res_1019_ = l_Lean_MVarId_admit(v_mvarId_1011_, v_synthetic_boxed_1018_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object* v_mvarId_1020_, lean_object* v_val_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_1020_, v_val_1021_, v___y_1023_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object* v_mvarId_1028_, lean_object* v_val_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(v_mvarId_1028_, v_val_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object* v_00_u03b2_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_1037_, v_x_1038_, v_x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1041_, lean_object* v_x_1042_, size_t v_x_1043_, size_t v_x_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_1042_, v_x_1043_, v_x_1044_, v_x_1045_, v_x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
size_t v_x_1336__boxed_1054_; size_t v_x_1337__boxed_1055_; lean_object* v_res_1056_; 
v_x_1336__boxed_1054_ = lean_unbox_usize(v_x_1050_);
lean_dec(v_x_1050_);
v_x_1337__boxed_1055_ = lean_unbox_usize(v_x_1051_);
lean_dec(v_x_1051_);
v_res_1056_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1048_, v_x_1049_, v_x_1336__boxed_1054_, v_x_1337__boxed_1055_, v_x_1052_, v_x_1053_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1057_, lean_object* v_n_1058_, lean_object* v_k_1059_, lean_object* v_v_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1058_, v_k_1059_, v_v_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1062_, size_t v_depth_1063_, lean_object* v_keys_1064_, lean_object* v_vals_1065_, lean_object* v_heq_1066_, lean_object* v_i_1067_, lean_object* v_entries_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1063_, v_keys_1064_, v_vals_1065_, v_i_1067_, v_entries_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1070_, lean_object* v_depth_1071_, lean_object* v_keys_1072_, lean_object* v_vals_1073_, lean_object* v_heq_1074_, lean_object* v_i_1075_, lean_object* v_entries_1076_){
_start:
{
size_t v_depth_boxed_1077_; lean_object* v_res_1078_; 
v_depth_boxed_1077_ = lean_unbox_usize(v_depth_1071_);
lean_dec(v_depth_1071_);
v_res_1078_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1070_, v_depth_boxed_1077_, v_keys_1072_, v_vals_1073_, v_heq_1074_, v_i_1075_, v_entries_1076_);
lean_dec_ref(v_vals_1073_);
lean_dec_ref(v_keys_1072_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1080_, v_x_1081_, v_x_1082_, v_x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object* v_mvarId_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; 
lean_inc(v_mvarId_1085_);
v___x_1091_ = l_Lean_MVarId_getType(v_mvarId_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v___x_1093_ = l_Lean_Expr_headBeta(v_a_1092_);
v___x_1094_ = l_Lean_MVarId_setType___redArg(v_mvarId_1085_, v___x_1093_, v_a_1087_);
return v___x_1094_;
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v_mvarId_1085_);
v_a_1095_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1091_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1091_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object* v_mvarId_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_MVarId_headBetaType(v_mvarId_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4___redArg(lean_object* v_m_1110_, lean_object* v_query_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v_zero_1115_; uint8_t v_isZero_1116_; 
v_zero_1115_ = lean_unsigned_to_nat(0u);
v_isZero_1116_ = lean_nat_dec_eq(v_x_1113_, v_zero_1115_);
if (v_isZero_1116_ == 1)
{
lean_dec(v_x_1114_);
lean_dec(v_x_1113_);
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_box(2);
return v___x_1117_;
}
else
{
lean_object* v_val_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_val_1118_ = lean_ctor_get(v_x_1112_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v_x_1112_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_val_1118_);
lean_dec(v_x_1112_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_val_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v_keyArray_1126_; lean_object* v_valueArray_1127_; lean_object* v___x_1128_; uint8_t v_isSome_1129_; 
v_keyArray_1126_ = lean_ctor_get(v_m_1110_, 1);
v_valueArray_1127_ = lean_ctor_get(v_m_1110_, 2);
v___x_1128_ = lean_array_fget_borrowed(v_keyArray_1126_, v_x_1114_);
v_isSome_1129_ = lean_noption_is_some(v___x_1128_);
if (v_isSome_1129_ == 0)
{
lean_dec(v_x_1113_);
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_x_1114_);
return v___x_1130_;
}
else
{
lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_x_1114_);
v_val_1131_ = lean_ctor_get(v_x_1112_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v_x_1112_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_dec(v_x_1112_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_val_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_one_1139_; lean_object* v_n_1140_; lean_object* v___y_1142_; 
v_one_1139_ = lean_unsigned_to_nat(1u);
v_n_1140_ = lean_nat_sub(v_x_1113_, v_one_1139_);
lean_dec(v_x_1113_);
if (v_isSome_1129_ == 0)
{
goto v___jp_1148_;
}
else
{
lean_object* v___x_1150_; uint8_t v_isSome_1151_; 
v___x_1150_ = lean_array_fget_borrowed(v_valueArray_1127_, v_x_1114_);
v_isSome_1151_ = lean_noption_is_some(v___x_1150_);
if (v_isSome_1151_ == 0)
{
goto v___jp_1148_;
}
else
{
lean_object* v_val_1152_; uint8_t v___x_1153_; 
lean_inc(v___x_1128_);
v_val_1152_ = lean_noption_get(v___x_1128_);
v___x_1153_ = l_Lean_instBEqFVarId_beq(v_val_1152_, v_query_1111_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
lean_dec(v_val_1152_);
v___x_1154_ = lean_array_get_size(v_keyArray_1126_);
v___x_1155_ = lean_nat_add(v_x_1114_, v_one_1139_);
lean_dec(v_x_1114_);
v___x_1156_ = lean_nat_dec_lt(v___x_1155_, v___x_1154_);
if (v___x_1156_ == 0)
{
lean_dec(v___x_1155_);
v_x_1113_ = v_n_1140_;
v_x_1114_ = v_zero_1115_;
goto _start;
}
else
{
v_x_1113_ = v_n_1140_;
v_x_1114_ = v___x_1155_;
goto _start;
}
}
else
{
lean_object* v_val_1159_; lean_object* v___x_1160_; 
lean_dec(v_n_1140_);
lean_dec(v_x_1112_);
lean_inc(v___x_1150_);
v_val_1159_ = lean_noption_get(v___x_1150_);
v___x_1160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1160_, 0, v_x_1114_);
lean_ctor_set(v___x_1160_, 1, v_val_1152_);
lean_ctor_set(v___x_1160_, 2, v_val_1159_);
return v___x_1160_;
}
}
}
v___jp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = lean_array_get_size(v_keyArray_1126_);
v___x_1144_ = lean_nat_add(v_x_1114_, v_one_1139_);
lean_dec(v_x_1114_);
v___x_1145_ = lean_nat_dec_lt(v___x_1144_, v___x_1143_);
if (v___x_1145_ == 0)
{
lean_dec(v___x_1144_);
v_x_1112_ = v___y_1142_;
v_x_1113_ = v_n_1140_;
v_x_1114_ = v_zero_1115_;
goto _start;
}
else
{
v_x_1112_ = v___y_1142_;
v_x_1113_ = v_n_1140_;
v_x_1114_ = v___x_1144_;
goto _start;
}
}
v___jp_1148_:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v___x_1149_; 
lean_inc(v_x_1114_);
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_x_1114_);
v___y_1142_ = v___x_1149_;
goto v___jp_1141_;
}
else
{
v___y_1142_ = v_x_1112_;
goto v___jp_1141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4___redArg___boxed(lean_object* v_m_1161_, lean_object* v_query_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4___redArg(v_m_1161_, v_query_1162_, v_x_1163_, v_x_1164_, v_x_1165_);
lean_dec(v_query_1162_);
lean_dec_ref(v_m_1161_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1167_, lean_object* v_query_1168_){
_start:
{
lean_object* v_keyArray_1169_; lean_object* v___x_1170_; uint64_t v___x_1171_; uint64_t v___x_1172_; uint64_t v___x_1173_; uint64_t v_fold_1174_; uint64_t v___x_1175_; uint64_t v___x_1176_; uint64_t v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_keyArray_1169_ = lean_ctor_get(v_m_1167_, 1);
v___x_1170_ = lean_array_get_size(v_keyArray_1169_);
v___x_1171_ = l_Lean_instHashableFVarId_hash(v_query_1168_);
v___x_1172_ = 32ULL;
v___x_1173_ = lean_uint64_shift_right(v___x_1171_, v___x_1172_);
v_fold_1174_ = lean_uint64_xor(v___x_1171_, v___x_1173_);
v___x_1175_ = 16ULL;
v___x_1176_ = lean_uint64_shift_right(v_fold_1174_, v___x_1175_);
v___x_1177_ = lean_uint64_xor(v_fold_1174_, v___x_1176_);
v___x_1178_ = lean_uint64_to_usize(v___x_1177_);
v___x_1179_ = lean_usize_of_nat(v___x_1170_);
v___x_1180_ = ((size_t)1ULL);
v___x_1181_ = lean_usize_sub(v___x_1179_, v___x_1180_);
v___x_1182_ = lean_usize_land(v___x_1178_, v___x_1181_);
v___x_1183_ = lean_usize_to_nat(v___x_1182_);
v___x_1184_ = lean_box(0);
v___x_1185_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4___redArg(v_m_1167_, v_query_1168_, v___x_1184_, v___x_1170_, v___x_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg___boxed(lean_object* v_m_1186_, lean_object* v_query_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_1186_, v_query_1187_);
lean_dec(v_query_1187_);
lean_dec_ref(v_m_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object* v_m_1189_, lean_object* v_query_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_1189_, v_query_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_index_1192_; lean_object* v_key_1193_; lean_object* v_value_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_index_1192_ = lean_ctor_get(v___x_1191_, 0);
v_key_1193_ = lean_ctor_get(v___x_1191_, 1);
v_value_1194_ = lean_ctor_get(v___x_1191_, 2);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1191_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_value_1194_);
lean_inc(v_key_1193_);
lean_inc(v_index_1192_);
lean_dec(v___x_1191_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_index_1192_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_key_1193_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_value_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v___x_1202_; 
lean_dec(v___x_1191_);
v___x_1202_ = lean_box(1);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object* v_m_1203_, lean_object* v_query_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_m_1203_, v_query_1204_);
lean_dec(v_query_1204_);
lean_dec_ref(v_m_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object* v_m_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_m_1206_, v_a_1207_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_index_1209_; lean_object* v_size_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_index_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_index_1209_);
lean_dec_ref_known(v___x_1208_, 3);
v_size_1210_ = lean_ctor_get(v_m_1206_, 0);
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_sub(v_size_1210_, v___x_1211_);
v___x_1213_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1206_, v___x_1212_, v_index_1209_);
lean_dec(v_index_1209_);
return v___x_1213_;
}
else
{
return v_m_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object* v_m_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_1214_, v_a_1215_);
lean_dec(v_a_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object* v_e_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1224_ = lean_st_ref_take(v___y_1218_);
v___x_1225_ = l_Lean_Expr_fvarId_x21(v_e_1217_);
v___x_1226_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1224_, v___x_1225_);
lean_dec(v___x_1225_);
v___x_1227_ = lean_st_ref_put(v___y_1218_, v___x_1226_);
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object* v_e_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_MVarId_getNondepPropHyps___lam__0(v_e_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v_e_1230_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object* v_____r_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_st_ref_get(v___y_1239_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object* v_____r_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_MVarId_getNondepPropHyps___lam__1(v_____r_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
return v_res_1254_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___redArg(lean_object* v_m_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_m_1255_, v_a_1256_);
if (lean_obj_tag(v___x_1257_) == 0)
{
uint8_t v___x_1258_; 
lean_dec_ref_known(v___x_1257_, 3);
v___x_1258_ = 1;
return v___x_1258_;
}
else
{
uint8_t v___x_1259_; 
v___x_1259_ = 0;
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___redArg___boxed(lean_object* v_m_1260_, lean_object* v_a_1261_){
_start:
{
uint8_t v_res_1262_; lean_object* v_r_1263_; 
v_res_1262_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___redArg(v_m_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_m_1260_);
v_r_1263_ = lean_box(v_res_1262_);
return v_r_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25___redArg(lean_object* v_a_1264_, lean_object* v_as_1265_, size_t v_sz_1266_, size_t v_i_1267_, lean_object* v_b_1268_){
_start:
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_usize_dec_lt(v_i_1267_, v_sz_1266_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v_b_1268_);
return v___x_1271_;
}
else
{
lean_object* v_snd_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1290_; 
v_snd_1272_ = lean_ctor_get(v_b_1268_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_b_1268_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v_b_1268_, 0);
lean_dec(v_unused_1291_);
v___x_1274_ = v_b_1268_;
v_isShared_1275_ = v_isSharedCheck_1290_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_snd_1272_);
lean_dec(v_b_1268_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1290_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v_a_1278_; lean_object* v_a_1285_; 
v___x_1276_ = lean_box(0);
v_a_1285_ = lean_array_uget_borrowed(v_as_1265_, v_i_1267_);
if (lean_obj_tag(v_a_1285_) == 0)
{
v_a_1278_ = v_snd_1272_;
goto v___jp_1277_;
}
else
{
lean_object* v_val_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_val_1286_ = lean_ctor_get(v_a_1285_, 0);
v___x_1287_ = l_Lean_LocalDecl_fvarId(v_val_1286_);
v___x_1288_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___redArg(v_a_1264_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_dec(v___x_1287_);
v_a_1278_ = v_snd_1272_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_array_push(v_snd_1272_, v___x_1287_);
v_a_1278_ = v___x_1289_;
goto v___jp_1277_;
}
}
v___jp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 1, v_a_1278_);
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1280_ = v___x_1274_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_a_1278_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
size_t v___x_1281_; size_t v___x_1282_; 
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = lean_usize_add(v_i_1267_, v___x_1281_);
v_i_1267_ = v___x_1282_;
v_b_1268_ = v___x_1280_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25___redArg___boxed(lean_object* v_a_1292_, lean_object* v_as_1293_, lean_object* v_sz_1294_, lean_object* v_i_1295_, lean_object* v_b_1296_, lean_object* v___y_1297_){
_start:
{
size_t v_sz_boxed_1298_; size_t v_i_boxed_1299_; lean_object* v_res_1300_; 
v_sz_boxed_1298_ = lean_unbox_usize(v_sz_1294_);
lean_dec(v_sz_1294_);
v_i_boxed_1299_ = lean_unbox_usize(v_i_1295_);
lean_dec(v_i_1295_);
v_res_1300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25___redArg(v_a_1292_, v_as_1293_, v_sz_boxed_1298_, v_i_boxed_1299_, v_b_1296_);
lean_dec_ref(v_as_1293_);
lean_dec_ref(v_a_1292_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20(lean_object* v_a_1301_, lean_object* v_as_1302_, size_t v_sz_1303_, size_t v_i_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_usize_dec_lt(v_i_1304_, v_sz_1303_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_b_1305_);
return v___x_1312_;
}
else
{
lean_object* v_snd_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1331_; 
v_snd_1313_ = lean_ctor_get(v_b_1305_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_b_1305_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v_b_1305_, 0);
lean_dec(v_unused_1332_);
v___x_1315_ = v_b_1305_;
v_isShared_1316_ = v_isSharedCheck_1331_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_snd_1313_);
lean_dec(v_b_1305_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1331_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v_a_1319_; lean_object* v_a_1326_; 
v___x_1317_ = lean_box(0);
v_a_1326_ = lean_array_uget_borrowed(v_as_1302_, v_i_1304_);
if (lean_obj_tag(v_a_1326_) == 0)
{
v_a_1319_ = v_snd_1313_;
goto v___jp_1318_;
}
else
{
lean_object* v_val_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_val_1327_ = lean_ctor_get(v_a_1326_, 0);
v___x_1328_ = l_Lean_LocalDecl_fvarId(v_val_1327_);
v___x_1329_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___redArg(v_a_1301_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_dec(v___x_1328_);
v_a_1319_ = v_snd_1313_;
goto v___jp_1318_;
}
else
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_array_push(v_snd_1313_, v___x_1328_);
v_a_1319_ = v___x_1330_;
goto v___jp_1318_;
}
}
v___jp_1318_:
{
lean_object* v___x_1321_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v_a_1319_);
lean_ctor_set(v___x_1315_, 0, v___x_1317_);
v___x_1321_ = v___x_1315_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_a_1319_);
v___x_1321_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((size_t)1ULL);
v___x_1323_ = lean_usize_add(v_i_1304_, v___x_1322_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25___redArg(v_a_1301_, v_as_1302_, v_sz_1303_, v___x_1323_, v___x_1321_);
return v___x_1324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20___boxed(lean_object* v_a_1333_, lean_object* v_as_1334_, lean_object* v_sz_1335_, lean_object* v_i_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
size_t v_sz_boxed_1343_; size_t v_i_boxed_1344_; lean_object* v_res_1345_; 
v_sz_boxed_1343_ = lean_unbox_usize(v_sz_1335_);
lean_dec(v_sz_1335_);
v_i_boxed_1344_ = lean_unbox_usize(v_i_1336_);
lean_dec(v_i_1336_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20(v_a_1333_, v_as_1334_, v_sz_boxed_1343_, v_i_boxed_1344_, v_b_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v_as_1334_);
lean_dec_ref(v_a_1333_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12(lean_object* v_init_1346_, lean_object* v_a_1347_, lean_object* v_n_1348_, lean_object* v_b_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
if (lean_obj_tag(v_n_1348_) == 0)
{
lean_object* v_cs_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; size_t v_sz_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
v_cs_1355_ = lean_ctor_get(v_n_1348_, 0);
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v_b_1349_);
v_sz_1358_ = lean_array_size(v_cs_1355_);
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__19(v_init_1346_, v_a_1347_, v_cs_1355_, v_sz_1358_, v___x_1359_, v___x_1357_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1375_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v_fst_1365_; 
v_fst_1365_ = lean_ctor_get(v_a_1361_, 0);
if (lean_obj_tag(v_fst_1365_) == 0)
{
lean_object* v_snd_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v_snd_1366_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_snd_1366_);
lean_dec(v_a_1361_);
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_snd_1366_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1367_);
v___x_1369_ = v___x_1363_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
else
{
lean_object* v_val_1371_; lean_object* v___x_1373_; 
lean_inc_ref(v_fst_1365_);
lean_dec(v_a_1361_);
v_val_1371_ = lean_ctor_get(v_fst_1365_, 0);
lean_inc(v_val_1371_);
lean_dec_ref_known(v_fst_1365_, 1);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v_val_1371_);
v___x_1373_ = v___x_1363_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_val_1371_);
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
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
v_a_1376_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1360_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1360_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v_vs_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; size_t v_sz_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v_vs_1384_ = lean_ctor_get(v_n_1348_, 0);
v___x_1385_ = lean_box(0);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v_b_1349_);
v_sz_1387_ = lean_array_size(v_vs_1384_);
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20(v_a_1347_, v_vs_1384_, v_sz_1387_, v___x_1388_, v___x_1386_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1404_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1404_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1404_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_fst_1394_; 
v_fst_1394_ = lean_ctor_get(v_a_1390_, 0);
if (lean_obj_tag(v_fst_1394_) == 0)
{
lean_object* v_snd_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v_snd_1395_ = lean_ctor_get(v_a_1390_, 1);
lean_inc(v_snd_1395_);
lean_dec(v_a_1390_);
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_snd_1395_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1396_);
v___x_1398_ = v___x_1392_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
else
{
lean_object* v_val_1400_; lean_object* v___x_1402_; 
lean_inc_ref(v_fst_1394_);
lean_dec(v_a_1390_);
v_val_1400_ = lean_ctor_get(v_fst_1394_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v_fst_1394_, 1);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v_val_1400_);
v___x_1402_ = v___x_1392_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_val_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1389_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1389_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__19(lean_object* v_init_1413_, lean_object* v_a_1414_, lean_object* v_as_1415_, size_t v_sz_1416_, size_t v_i_1417_, lean_object* v_b_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_usize_dec_lt(v_i_1417_, v_sz_1416_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_b_1418_);
return v___x_1425_;
}
else
{
lean_object* v_snd_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1460_; 
v_snd_1426_ = lean_ctor_get(v_b_1418_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_b_1418_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_b_1418_, 0);
lean_dec(v_unused_1461_);
v___x_1428_ = v_b_1418_;
v_isShared_1429_ = v_isSharedCheck_1460_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_snd_1426_);
lean_dec(v_b_1418_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1460_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v_a_1430_; lean_object* v___x_1431_; 
v_a_1430_ = lean_array_uget_borrowed(v_as_1415_, v_i_1417_);
lean_inc(v_snd_1426_);
v___x_1431_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12(v_init_1413_, v_a_1414_, v_a_1430_, v_snd_1426_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1451_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1451_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1451_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
if (lean_obj_tag(v_a_1432_) == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1432_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1436_);
v___x_1438_ = v___x_1428_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_snd_1426_);
v___x_1438_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
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
lean_object* v_a_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_del_object(v___x_1434_);
lean_dec(v_snd_1426_);
v_a_1443_ = lean_ctor_get(v_a_1432_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v_a_1432_, 1);
v___x_1444_ = lean_box(0);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 1, v_a_1443_);
lean_ctor_set(v___x_1428_, 0, v___x_1444_);
v___x_1446_ = v___x_1428_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_a_1443_);
v___x_1446_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
size_t v___x_1447_; size_t v___x_1448_; 
v___x_1447_ = ((size_t)1ULL);
v___x_1448_ = lean_usize_add(v_i_1417_, v___x_1447_);
v_i_1417_ = v___x_1448_;
v_b_1418_ = v___x_1446_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_del_object(v___x_1428_);
lean_dec(v_snd_1426_);
v_a_1452_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1431_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1431_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__19___boxed(lean_object* v_init_1462_, lean_object* v_a_1463_, lean_object* v_as_1464_, lean_object* v_sz_1465_, lean_object* v_i_1466_, lean_object* v_b_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
size_t v_sz_boxed_1473_; size_t v_i_boxed_1474_; lean_object* v_res_1475_; 
v_sz_boxed_1473_ = lean_unbox_usize(v_sz_1465_);
lean_dec(v_sz_1465_);
v_i_boxed_1474_ = lean_unbox_usize(v_i_1466_);
lean_dec(v_i_1466_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__19(v_init_1462_, v_a_1463_, v_as_1464_, v_sz_boxed_1473_, v_i_boxed_1474_, v_b_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_as_1464_);
lean_dec_ref(v_a_1463_);
lean_dec_ref(v_init_1462_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12___boxed(lean_object* v_init_1476_, lean_object* v_a_1477_, lean_object* v_n_1478_, lean_object* v_b_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12(v_init_1476_, v_a_1477_, v_n_1478_, v_b_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec_ref(v_n_1478_);
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_init_1476_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22___redArg(lean_object* v_a_1486_, lean_object* v_as_1487_, size_t v_sz_1488_, size_t v_i_1489_, lean_object* v_b_1490_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_usize_dec_lt(v_i_1489_, v_sz_1488_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_b_1490_);
return v___x_1493_;
}
else
{
lean_object* v_snd_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1512_; 
v_snd_1494_ = lean_ctor_get(v_b_1490_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_b_1490_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_b_1490_, 0);
lean_dec(v_unused_1513_);
v___x_1496_ = v_b_1490_;
v_isShared_1497_ = v_isSharedCheck_1512_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snd_1494_);
lean_dec(v_b_1490_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1512_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v_a_1500_; lean_object* v_a_1507_; 
v___x_1498_ = lean_box(0);
v_a_1507_ = lean_array_uget_borrowed(v_as_1487_, v_i_1489_);
if (lean_obj_tag(v_a_1507_) == 0)
{
v_a_1500_ = v_snd_1494_;
goto v___jp_1499_;
}
else
{
lean_object* v_val_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_val_1508_ = lean_ctor_get(v_a_1507_, 0);
v___x_1509_ = l_Lean_LocalDecl_fvarId(v_val_1508_);
v___x_1510_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___redArg(v_a_1486_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_dec(v___x_1509_);
v_a_1500_ = v_snd_1494_;
goto v___jp_1499_;
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_array_push(v_snd_1494_, v___x_1509_);
v_a_1500_ = v___x_1511_;
goto v___jp_1499_;
}
}
v___jp_1499_:
{
lean_object* v___x_1502_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v_a_1500_);
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1502_ = v___x_1496_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_a_1500_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
size_t v___x_1503_; size_t v___x_1504_; 
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1489_, v___x_1503_);
v_i_1489_ = v___x_1504_;
v_b_1490_ = v___x_1502_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22___redArg___boxed(lean_object* v_a_1514_, lean_object* v_as_1515_, lean_object* v_sz_1516_, lean_object* v_i_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_){
_start:
{
size_t v_sz_boxed_1520_; size_t v_i_boxed_1521_; lean_object* v_res_1522_; 
v_sz_boxed_1520_ = lean_unbox_usize(v_sz_1516_);
lean_dec(v_sz_1516_);
v_i_boxed_1521_ = lean_unbox_usize(v_i_1517_);
lean_dec(v_i_1517_);
v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22___redArg(v_a_1514_, v_as_1515_, v_sz_boxed_1520_, v_i_boxed_1521_, v_b_1518_);
lean_dec_ref(v_as_1515_);
lean_dec_ref(v_a_1514_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13(lean_object* v_a_1523_, lean_object* v_as_1524_, size_t v_sz_1525_, size_t v_i_1526_, lean_object* v_b_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_usize_dec_lt(v_i_1526_, v_sz_1525_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_b_1527_);
return v___x_1534_;
}
else
{
lean_object* v_snd_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1553_; 
v_snd_1535_ = lean_ctor_get(v_b_1527_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_b_1527_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v_b_1527_, 0);
lean_dec(v_unused_1554_);
v___x_1537_ = v_b_1527_;
v_isShared_1538_ = v_isSharedCheck_1553_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_snd_1535_);
lean_dec(v_b_1527_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1553_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v_a_1541_; lean_object* v_a_1548_; 
v___x_1539_ = lean_box(0);
v_a_1548_ = lean_array_uget_borrowed(v_as_1524_, v_i_1526_);
if (lean_obj_tag(v_a_1548_) == 0)
{
v_a_1541_ = v_snd_1535_;
goto v___jp_1540_;
}
else
{
lean_object* v_val_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_val_1549_ = lean_ctor_get(v_a_1548_, 0);
v___x_1550_ = l_Lean_LocalDecl_fvarId(v_val_1549_);
v___x_1551_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___redArg(v_a_1523_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_dec(v___x_1550_);
v_a_1541_ = v_snd_1535_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_array_push(v_snd_1535_, v___x_1550_);
v_a_1541_ = v___x_1552_;
goto v___jp_1540_;
}
}
v___jp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v_a_1541_);
lean_ctor_set(v___x_1537_, 0, v___x_1539_);
v___x_1543_ = v___x_1537_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_a_1541_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
size_t v___x_1544_; size_t v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = ((size_t)1ULL);
v___x_1545_ = lean_usize_add(v_i_1526_, v___x_1544_);
v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22___redArg(v_a_1523_, v_as_1524_, v_sz_1525_, v___x_1545_, v___x_1543_);
return v___x_1546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13___boxed(lean_object* v_a_1555_, lean_object* v_as_1556_, lean_object* v_sz_1557_, lean_object* v_i_1558_, lean_object* v_b_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
size_t v_sz_boxed_1565_; size_t v_i_boxed_1566_; lean_object* v_res_1567_; 
v_sz_boxed_1565_ = lean_unbox_usize(v_sz_1557_);
lean_dec(v_sz_1557_);
v_i_boxed_1566_ = lean_unbox_usize(v_i_1558_);
lean_dec(v_i_1558_);
v_res_1567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13(v_a_1555_, v_as_1556_, v_sz_boxed_1565_, v_i_boxed_1566_, v_b_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v_as_1556_);
lean_dec_ref(v_a_1555_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6(lean_object* v_a_1568_, lean_object* v_t_1569_, lean_object* v_init_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_root_1576_; lean_object* v_tail_1577_; lean_object* v___x_1578_; 
v_root_1576_ = lean_ctor_get(v_t_1569_, 0);
v_tail_1577_ = lean_ctor_get(v_t_1569_, 1);
lean_inc_ref(v_init_1570_);
v___x_1578_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12(v_init_1570_, v_a_1568_, v_root_1576_, v_init_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec_ref(v_init_1570_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1615_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1615_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1615_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
if (lean_obj_tag(v_a_1579_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; 
v_a_1583_ = lean_ctor_get(v_a_1579_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v_a_1579_, 1);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v_a_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; size_t v_sz_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
lean_del_object(v___x_1581_);
v_a_1587_ = lean_ctor_get(v_a_1579_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v_a_1579_, 1);
v___x_1588_ = lean_box(0);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v_a_1587_);
v_sz_1590_ = lean_array_size(v_tail_1577_);
v___x_1591_ = ((size_t)0ULL);
v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13(v_a_1568_, v_tail_1577_, v_sz_1590_, v___x_1591_, v___x_1589_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1606_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1606_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1606_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_fst_1597_; 
v_fst_1597_ = lean_ctor_get(v_a_1593_, 0);
if (lean_obj_tag(v_fst_1597_) == 0)
{
lean_object* v_snd_1598_; lean_object* v___x_1600_; 
v_snd_1598_ = lean_ctor_get(v_a_1593_, 1);
lean_inc(v_snd_1598_);
lean_dec(v_a_1593_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_snd_1598_);
v___x_1600_ = v___x_1595_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_snd_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
else
{
lean_object* v_val_1602_; lean_object* v___x_1604_; 
lean_inc_ref(v_fst_1597_);
lean_dec(v_a_1593_);
v_val_1602_ = lean_ctor_get(v_fst_1597_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v_fst_1597_, 1);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_val_1602_);
v___x_1604_ = v___x_1595_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_val_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1592_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1592_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_a_1616_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1578_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1578_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6___boxed(lean_object* v_a_1624_, lean_object* v_t_1625_, lean_object* v_init_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6(v_a_1624_, v_t_1625_, v_init_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec_ref(v_t_1625_);
lean_dec_ref(v_a_1624_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3___redArg(lean_object* v_e_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v___x_1636_; lean_object* v_visited_1637_; size_t v___x_1638_; size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; size_t v___x_1642_; uint8_t v___x_1643_; 
v___x_1636_ = lean_st_ref_get(v_a_1634_);
v_visited_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc_ref(v_visited_1637_);
lean_dec(v___x_1636_);
v___x_1638_ = lean_ptr_addr(v_e_1633_);
v___x_1639_ = ((size_t)8191ULL);
v___x_1640_ = lean_usize_mod(v___x_1638_, v___x_1639_);
v___x_1641_ = lean_array_uget(v_visited_1637_, v___x_1640_);
lean_dec_ref(v_visited_1637_);
v___x_1642_ = lean_ptr_addr(v___x_1641_);
lean_dec(v___x_1641_);
v___x_1643_ = lean_usize_dec_eq(v___x_1642_, v___x_1638_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v_visited_1645_; lean_object* v_checked_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1657_; 
v___x_1644_ = lean_st_ref_take(v_a_1634_);
v_visited_1645_ = lean_ctor_get(v___x_1644_, 0);
v_checked_1646_ = lean_ctor_get(v___x_1644_, 1);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1648_ = v___x_1644_;
v_isShared_1649_ = v_isSharedCheck_1657_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_checked_1646_);
lean_inc(v_visited_1645_);
lean_dec(v___x_1644_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1657_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_array_uset(v_visited_1645_, v___x_1640_, v_e_1633_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_checked_1646_);
v___x_1652_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_st_ref_put(v_a_1634_, v___x_1652_);
v___x_1654_ = lean_box(v___x_1643_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec_ref(v_e_1633_);
v___x_1658_ = lean_box(v___x_1643_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_e_1660_, lean_object* v_a_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3___redArg(v_e_1660_, v_a_1661_);
lean_dec(v_a_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19___redArg(lean_object* v_m_1664_, lean_object* v_query_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v_zero_1669_; uint8_t v_isZero_1670_; 
v_zero_1669_ = lean_unsigned_to_nat(0u);
v_isZero_1670_ = lean_nat_dec_eq(v_x_1667_, v_zero_1669_);
if (v_isZero_1670_ == 1)
{
lean_dec(v_x_1668_);
lean_dec(v_x_1667_);
if (lean_obj_tag(v_x_1666_) == 0)
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_box(2);
return v___x_1671_;
}
else
{
lean_object* v_val_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
v_val_1672_ = lean_ctor_get(v_x_1666_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_x_1666_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v_x_1666_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_val_1672_);
lean_dec(v_x_1666_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_val_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_keyArray_1680_; lean_object* v_valueArray_1681_; lean_object* v___x_1682_; uint8_t v_isSome_1683_; 
v_keyArray_1680_ = lean_ctor_get(v_m_1664_, 1);
v_valueArray_1681_ = lean_ctor_get(v_m_1664_, 2);
v___x_1682_ = lean_array_fget_borrowed(v_keyArray_1680_, v_x_1668_);
v_isSome_1683_ = lean_noption_is_some(v___x_1682_);
if (v_isSome_1683_ == 0)
{
lean_dec(v_x_1667_);
if (lean_obj_tag(v_x_1666_) == 0)
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_x_1668_);
return v___x_1684_;
}
else
{
lean_object* v_val_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_x_1668_);
v_val_1685_ = lean_ctor_get(v_x_1666_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1666_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v_x_1666_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_val_1685_);
lean_dec(v_x_1666_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_val_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_object* v_one_1693_; lean_object* v_n_1694_; lean_object* v___y_1696_; 
v_one_1693_ = lean_unsigned_to_nat(1u);
v_n_1694_ = lean_nat_sub(v_x_1667_, v_one_1693_);
lean_dec(v_x_1667_);
if (v_isSome_1683_ == 0)
{
goto v___jp_1702_;
}
else
{
lean_object* v___x_1704_; uint8_t v_isSome_1705_; 
v___x_1704_ = lean_array_fget_borrowed(v_valueArray_1681_, v_x_1668_);
v_isSome_1705_ = lean_noption_is_some(v___x_1704_);
if (v_isSome_1705_ == 0)
{
goto v___jp_1702_;
}
else
{
lean_object* v_val_1706_; uint8_t v___x_1707_; 
lean_inc(v___x_1682_);
v_val_1706_ = lean_noption_get(v___x_1682_);
v___x_1707_ = lean_expr_eqv(v_val_1706_, v_query_1665_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
lean_dec(v_val_1706_);
v___x_1708_ = lean_array_get_size(v_keyArray_1680_);
v___x_1709_ = lean_nat_add(v_x_1668_, v_one_1693_);
lean_dec(v_x_1668_);
v___x_1710_ = lean_nat_dec_lt(v___x_1709_, v___x_1708_);
if (v___x_1710_ == 0)
{
lean_dec(v___x_1709_);
v_x_1667_ = v_n_1694_;
v_x_1668_ = v_zero_1669_;
goto _start;
}
else
{
v_x_1667_ = v_n_1694_;
v_x_1668_ = v___x_1709_;
goto _start;
}
}
else
{
lean_object* v_val_1713_; lean_object* v___x_1714_; 
lean_dec(v_n_1694_);
lean_dec(v_x_1666_);
lean_inc(v___x_1704_);
v_val_1713_ = lean_noption_get(v___x_1704_);
v___x_1714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1714_, 0, v_x_1668_);
lean_ctor_set(v___x_1714_, 1, v_val_1706_);
lean_ctor_set(v___x_1714_, 2, v_val_1713_);
return v___x_1714_;
}
}
}
v___jp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1697_ = lean_array_get_size(v_keyArray_1680_);
v___x_1698_ = lean_nat_add(v_x_1668_, v_one_1693_);
lean_dec(v_x_1668_);
v___x_1699_ = lean_nat_dec_lt(v___x_1698_, v___x_1697_);
if (v___x_1699_ == 0)
{
lean_dec(v___x_1698_);
v_x_1666_ = v___y_1696_;
v_x_1667_ = v_n_1694_;
v_x_1668_ = v_zero_1669_;
goto _start;
}
else
{
v_x_1666_ = v___y_1696_;
v_x_1667_ = v_n_1694_;
v_x_1668_ = v___x_1698_;
goto _start;
}
}
v___jp_1702_:
{
if (lean_obj_tag(v_x_1666_) == 0)
{
lean_object* v___x_1703_; 
lean_inc(v_x_1668_);
v___x_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_x_1668_);
v___y_1696_ = v___x_1703_;
goto v___jp_1695_;
}
else
{
v___y_1696_ = v_x_1666_;
goto v___jp_1695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19___redArg___boxed(lean_object* v_m_1715_, lean_object* v_query_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19___redArg(v_m_1715_, v_query_1716_, v_x_1717_, v_x_1718_, v_x_1719_);
lean_dec_ref(v_query_1716_);
lean_dec_ref(v_m_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg(lean_object* v_m_1721_, lean_object* v_query_1722_){
_start:
{
lean_object* v_keyArray_1723_; lean_object* v___x_1724_; uint64_t v___x_1725_; uint64_t v___x_1726_; uint64_t v___x_1727_; uint64_t v_fold_1728_; uint64_t v___x_1729_; uint64_t v___x_1730_; uint64_t v___x_1731_; size_t v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_keyArray_1723_ = lean_ctor_get(v_m_1721_, 1);
v___x_1724_ = lean_array_get_size(v_keyArray_1723_);
v___x_1725_ = l_Lean_Expr_hash(v_query_1722_);
v___x_1726_ = 32ULL;
v___x_1727_ = lean_uint64_shift_right(v___x_1725_, v___x_1726_);
v_fold_1728_ = lean_uint64_xor(v___x_1725_, v___x_1727_);
v___x_1729_ = 16ULL;
v___x_1730_ = lean_uint64_shift_right(v_fold_1728_, v___x_1729_);
v___x_1731_ = lean_uint64_xor(v_fold_1728_, v___x_1730_);
v___x_1732_ = lean_uint64_to_usize(v___x_1731_);
v___x_1733_ = lean_usize_of_nat(v___x_1724_);
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_sub(v___x_1733_, v___x_1734_);
v___x_1736_ = lean_usize_land(v___x_1732_, v___x_1735_);
v___x_1737_ = lean_usize_to_nat(v___x_1736_);
v___x_1738_ = lean_box(0);
v___x_1739_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19___redArg(v_m_1721_, v_query_1722_, v___x_1738_, v___x_1724_, v___x_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg___boxed(lean_object* v_m_1740_, lean_object* v_query_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg(v_m_1740_, v_query_1741_);
lean_dec_ref(v_query_1741_);
lean_dec_ref(v_m_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17___redArg(lean_object* v_m_1743_, lean_object* v_query_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg(v_m_1743_, v_query_1744_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_index_1746_; lean_object* v_key_1747_; lean_object* v_value_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
v_index_1746_ = lean_ctor_get(v___x_1745_, 0);
v_key_1747_ = lean_ctor_get(v___x_1745_, 1);
v_value_1748_ = lean_ctor_get(v___x_1745_, 2);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1745_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_value_1748_);
lean_inc(v_key_1747_);
lean_inc(v_index_1746_);
lean_dec(v___x_1745_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_index_1746_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_key_1747_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_value_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
else
{
lean_object* v___x_1756_; 
lean_dec(v___x_1745_);
v___x_1756_ = lean_box(1);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17___redArg___boxed(lean_object* v_m_1757_, lean_object* v_query_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17___redArg(v_m_1757_, v_query_1758_);
lean_dec_ref(v_query_1758_);
lean_dec_ref(v_m_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10___redArg(lean_object* v_m_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17___redArg(v_m_1760_, v_a_1761_);
if (lean_obj_tag(v___x_1762_) == 0)
{
uint8_t v___x_1763_; 
lean_dec_ref_known(v___x_1762_, 3);
v___x_1763_ = 1;
return v___x_1763_;
}
else
{
uint8_t v___x_1764_; 
v___x_1764_ = 0;
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10___redArg___boxed(lean_object* v_m_1765_, lean_object* v_a_1766_){
_start:
{
uint8_t v_res_1767_; lean_object* v_r_1768_; 
v_res_1767_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10___redArg(v_m_1765_, v_a_1766_);
lean_dec_ref(v_a_1766_);
lean_dec_ref(v_m_1765_);
v_r_1768_ = lean_box(v_res_1767_);
return v_r_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29___redArg(lean_object* v_b_1769_, lean_object* v_acc_1770_, lean_object* v_i_1771_){
_start:
{
lean_object* v___y_1773_; lean_object* v_keyArray_1781_; lean_object* v_valueArray_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v_keyArray_1781_ = lean_ctor_get(v_b_1769_, 1);
v_valueArray_1782_ = lean_ctor_get(v_b_1769_, 2);
v___x_1783_ = lean_array_get_size(v_keyArray_1781_);
v___x_1784_ = lean_nat_dec_lt(v_i_1771_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_dec(v_i_1771_);
return v_acc_1770_;
}
else
{
lean_object* v___x_1785_; uint8_t v_isSome_1786_; 
v___x_1785_ = lean_array_fget_borrowed(v_keyArray_1781_, v_i_1771_);
v_isSome_1786_ = lean_noption_is_some(v___x_1785_);
if (v_isSome_1786_ == 0)
{
goto v___jp_1777_;
}
else
{
lean_object* v___x_1787_; uint8_t v_isSome_1788_; 
v___x_1787_ = lean_array_fget_borrowed(v_valueArray_1782_, v_i_1771_);
v_isSome_1788_ = lean_noption_is_some(v___x_1787_);
if (v_isSome_1788_ == 0)
{
goto v___jp_1777_;
}
else
{
lean_object* v_val_1789_; lean_object* v_val_1790_; lean_object* v_i_1792_; lean_object* v___x_1797_; 
lean_inc(v___x_1785_);
v_val_1789_ = lean_noption_get(v___x_1785_);
lean_inc(v___x_1787_);
v_val_1790_ = lean_noption_get(v___x_1787_);
v___x_1797_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg(v_acc_1770_, v_val_1789_);
switch(lean_obj_tag(v___x_1797_))
{
case 0:
{
lean_object* v_index_1798_; lean_object* v_size_1799_; lean_object* v___x_1800_; 
v_index_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_index_1798_);
lean_dec_ref_known(v___x_1797_, 3);
v_size_1799_ = lean_ctor_get(v_acc_1770_, 0);
lean_inc(v_size_1799_);
v___x_1800_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1770_, v_size_1799_, v_index_1798_, v_val_1789_, v_val_1790_);
lean_dec(v_index_1798_);
v___y_1773_ = v___x_1800_;
goto v___jp_1772_;
}
case 1:
{
lean_object* v_index_1801_; 
v_index_1801_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_index_1801_);
lean_dec_ref_known(v___x_1797_, 1);
v_i_1792_ = v_index_1801_;
goto v___jp_1791_;
}
default: 
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1770_, v___x_1802_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_index_1804_; 
v_index_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_index_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v_i_1792_ = v_index_1804_;
goto v___jp_1791_;
}
else
{
lean_dec(v_val_1790_);
lean_dec(v_val_1789_);
v___y_1773_ = v_acc_1770_;
goto v___jp_1772_;
}
}
}
v___jp_1791_:
{
lean_object* v_size_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_size_1793_ = lean_ctor_get(v_acc_1770_, 0);
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = lean_nat_add(v_size_1793_, v___x_1794_);
v___x_1796_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1770_, v___x_1795_, v_i_1792_, v_val_1789_, v_val_1790_);
lean_dec(v_i_1792_);
v___y_1773_ = v___x_1796_;
goto v___jp_1772_;
}
}
}
}
v___jp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = lean_nat_add(v_i_1771_, v___x_1774_);
lean_dec(v_i_1771_);
v_acc_1770_ = v___y_1773_;
v_i_1771_ = v___x_1775_;
goto _start;
}
v___jp_1777_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_nat_add(v_i_1771_, v___x_1778_);
lean_dec(v_i_1771_);
v_i_1771_ = v___x_1779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29___redArg___boxed(lean_object* v_b_1805_, lean_object* v_acc_1806_, lean_object* v_i_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29___redArg(v_b_1805_, v_acc_1806_, v_i_1807_);
lean_dec_ref(v_b_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21___redArg(lean_object* v_init_1809_, lean_object* v_b_1810_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29___redArg(v_b_1810_, v_init_1809_, v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21___redArg___boxed(lean_object* v_init_1813_, lean_object* v_b_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21___redArg(v_init_1813_, v_b_1814_);
lean_dec_ref(v_b_1814_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___redArg(lean_object* v_m_1816_){
_start:
{
lean_object* v_keyArray_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v_cellCount_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_target_1824_; lean_object* v___x_1825_; 
v_keyArray_1817_ = lean_ctor_get(v_m_1816_, 1);
v___x_1818_ = lean_array_get_size(v_keyArray_1817_);
v___x_1819_ = lean_unsigned_to_nat(2u);
v_cellCount_1820_ = lean_nat_mul(v___x_1818_, v___x_1819_);
v___x_1821_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1820_);
v___x_1822_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1820_);
v___x_1823_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1820_);
v_target_1824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1824_, 0, v___x_1821_);
lean_ctor_set(v_target_1824_, 1, v___x_1822_);
lean_ctor_set(v_target_1824_, 2, v___x_1823_);
v___x_1825_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21___redArg(v_target_1824_, v_m_1816_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___redArg___boxed(lean_object* v_m_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___redArg(v_m_1826_);
lean_dec_ref(v_m_1826_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4___redArg(lean_object* v_e_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v___x_1831_; lean_object* v_checked_1832_; uint8_t v___x_1833_; 
v___x_1831_ = lean_st_ref_get(v_a_1829_);
v_checked_1832_ = lean_ctor_get(v___x_1831_, 1);
lean_inc_ref(v_checked_1832_);
lean_dec(v___x_1831_);
v___x_1833_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10___redArg(v_checked_1832_, v_e_1828_);
lean_dec_ref(v_checked_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v_visited_1835_; lean_object* v_checked_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1910_; 
v___x_1834_ = lean_st_ref_take(v_a_1829_);
v_visited_1835_ = lean_ctor_get(v___x_1834_, 0);
v_checked_1836_ = lean_ctor_get(v___x_1834_, 1);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1838_ = v___x_1834_;
v_isShared_1839_ = v_isSharedCheck_1910_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_checked_1836_);
lean_inc(v_visited_1835_);
lean_dec(v___x_1834_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1910_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___y_1841_; lean_object* v___x_1848_; lean_object* v___y_1850_; lean_object* v_i_1851_; lean_object* v___y_1857_; lean_object* v___y_1867_; lean_object* v_i_1868_; lean_object* v___x_1883_; 
v___x_1848_ = lean_box(0);
v___x_1883_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg(v_checked_1836_, v_e_1828_);
switch(lean_obj_tag(v___x_1883_))
{
case 0:
{
lean_dec_ref_known(v___x_1883_, 3);
lean_dec_ref(v_e_1828_);
v___y_1841_ = v_checked_1836_;
goto v___jp_1840_;
}
case 1:
{
lean_object* v_index_1884_; lean_object* v_size_1885_; lean_object* v_keyArray_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v_index_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_index_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v_size_1885_ = lean_ctor_get(v_checked_1836_, 0);
v_keyArray_1886_ = lean_ctor_get(v_checked_1836_, 1);
v___x_1887_ = lean_unsigned_to_nat(1u);
v___x_1888_ = lean_nat_add(v_size_1885_, v___x_1887_);
v___x_1889_ = lean_array_get_size(v_keyArray_1886_);
v___x_1890_ = lean_nat_dec_lt(v___x_1888_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_dec(v___x_1888_);
lean_dec(v_index_1884_);
goto v___jp_1873_;
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1891_ = lean_unsigned_to_nat(4u);
v___x_1892_ = lean_nat_mul(v___x_1888_, v___x_1891_);
v___x_1893_ = lean_unsigned_to_nat(3u);
v___x_1894_ = lean_nat_mul(v___x_1889_, v___x_1893_);
v___x_1895_ = lean_nat_dec_le(v___x_1892_, v___x_1894_);
lean_dec(v___x_1894_);
lean_dec(v___x_1892_);
if (v___x_1895_ == 0)
{
lean_dec(v___x_1888_);
lean_dec(v_index_1884_);
goto v___jp_1873_;
}
else
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Std_DHashMap_Raw_setEntry___redArg(v_checked_1836_, v___x_1888_, v_index_1884_, v_e_1828_, v___x_1848_);
lean_dec(v_index_1884_);
v___y_1841_ = v___x_1896_;
goto v___jp_1840_;
}
}
}
default: 
{
lean_object* v_size_1897_; lean_object* v_keyArray_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v_size_1897_ = lean_ctor_get(v_checked_1836_, 0);
v_keyArray_1898_ = lean_ctor_get(v_checked_1836_, 1);
v___x_1899_ = lean_unsigned_to_nat(1u);
v___x_1900_ = lean_nat_add(v_size_1897_, v___x_1899_);
v___x_1901_ = lean_array_get_size(v_keyArray_1898_);
v___x_1902_ = lean_nat_dec_lt(v___x_1900_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
lean_dec(v___x_1900_);
v___x_1903_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___redArg(v_checked_1836_);
lean_dec_ref(v_checked_1836_);
v___y_1857_ = v___x_1903_;
goto v___jp_1856_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1904_ = lean_unsigned_to_nat(4u);
v___x_1905_ = lean_nat_mul(v___x_1900_, v___x_1904_);
lean_dec(v___x_1900_);
v___x_1906_ = lean_unsigned_to_nat(3u);
v___x_1907_ = lean_nat_mul(v___x_1901_, v___x_1906_);
v___x_1908_ = lean_nat_dec_le(v___x_1905_, v___x_1907_);
lean_dec(v___x_1907_);
lean_dec(v___x_1905_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___redArg(v_checked_1836_);
lean_dec_ref(v_checked_1836_);
v___y_1857_ = v___x_1909_;
goto v___jp_1856_;
}
else
{
v___y_1857_ = v_checked_1836_;
goto v___jp_1856_;
}
}
}
}
v___jp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 1, v___y_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_visited_1835_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___y_1841_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_st_ref_put(v_a_1829_, v___x_1843_);
v___x_1845_ = lean_box(v___x_1833_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
}
v___jp_1849_:
{
lean_object* v_size_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_size_1852_ = lean_ctor_get(v___y_1850_, 0);
v___x_1853_ = lean_unsigned_to_nat(1u);
v___x_1854_ = lean_nat_add(v_size_1852_, v___x_1853_);
v___x_1855_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1850_, v___x_1854_, v_i_1851_, v_e_1828_, v___x_1848_);
lean_dec(v_i_1851_);
v___y_1841_ = v___x_1855_;
goto v___jp_1840_;
}
v___jp_1856_:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg(v___y_1857_, v_e_1828_);
switch(lean_obj_tag(v___x_1858_))
{
case 0:
{
lean_object* v_index_1859_; lean_object* v_size_1860_; lean_object* v___x_1861_; 
v_index_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_index_1859_);
lean_dec_ref_known(v___x_1858_, 3);
v_size_1860_ = lean_ctor_get(v___y_1857_, 0);
lean_inc(v_size_1860_);
v___x_1861_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1857_, v_size_1860_, v_index_1859_, v_e_1828_, v___x_1848_);
lean_dec(v_index_1859_);
v___y_1841_ = v___x_1861_;
goto v___jp_1840_;
}
case 1:
{
lean_object* v_index_1862_; 
v_index_1862_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_index_1862_);
lean_dec_ref_known(v___x_1858_, 1);
v___y_1850_ = v___y_1857_;
v_i_1851_ = v_index_1862_;
goto v___jp_1849_;
}
default: 
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1857_, v___x_1863_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_index_1865_; 
v_index_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_index_1865_);
lean_dec_ref_known(v___x_1864_, 1);
v___y_1850_ = v___y_1857_;
v_i_1851_ = v_index_1865_;
goto v___jp_1849_;
}
else
{
lean_dec_ref(v_e_1828_);
v___y_1841_ = v___y_1857_;
goto v___jp_1840_;
}
}
}
}
v___jp_1866_:
{
lean_object* v_size_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_size_1869_ = lean_ctor_get(v___y_1867_, 0);
v___x_1870_ = lean_unsigned_to_nat(1u);
v___x_1871_ = lean_nat_add(v_size_1869_, v___x_1870_);
v___x_1872_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1867_, v___x_1871_, v_i_1868_, v_e_1828_, v___x_1848_);
lean_dec(v_i_1868_);
v___y_1841_ = v___x_1872_;
goto v___jp_1840_;
}
v___jp_1873_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___redArg(v_checked_1836_);
lean_dec_ref(v_checked_1836_);
v___x_1875_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg(v___x_1874_, v_e_1828_);
switch(lean_obj_tag(v___x_1875_))
{
case 0:
{
lean_object* v_index_1876_; lean_object* v_size_1877_; lean_object* v___x_1878_; 
v_index_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_index_1876_);
lean_dec_ref_known(v___x_1875_, 3);
v_size_1877_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_size_1877_);
v___x_1878_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1874_, v_size_1877_, v_index_1876_, v_e_1828_, v___x_1848_);
lean_dec(v_index_1876_);
v___y_1841_ = v___x_1878_;
goto v___jp_1840_;
}
case 1:
{
lean_object* v_index_1879_; 
v_index_1879_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_index_1879_);
lean_dec_ref_known(v___x_1875_, 1);
v___y_1867_ = v___x_1874_;
v_i_1868_ = v_index_1879_;
goto v___jp_1866_;
}
default: 
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1874_, v___x_1880_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_index_1882_; 
v_index_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_index_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v___y_1867_ = v___x_1874_;
v_i_1868_ = v_index_1882_;
goto v___jp_1866_;
}
else
{
lean_dec_ref(v_e_1828_);
v___y_1841_ = v___x_1874_;
goto v___jp_1840_;
}
}
}
}
}
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_dec_ref(v_e_1828_);
v___x_1911_ = lean_box(v___x_1833_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_e_1913_, lean_object* v_a_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4___redArg(v_e_1913_, v_a_1914_);
lean_dec(v_a_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2(lean_object* v_p_1917_, lean_object* v_f_1918_, uint8_t v_stopWhenVisited_1919_, lean_object* v_e_1920_, lean_object* v_a_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v_d_1934_; lean_object* v_b_1935_; lean_object* v___y_1936_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___x_1966_; 
lean_inc_ref(v_e_1920_);
v___x_1966_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3___redArg(v_e_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1999_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1999_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1999_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_unbox(v_a_1967_);
lean_dec(v_a_1967_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
lean_del_object(v___x_1969_);
lean_inc_ref(v_p_1917_);
lean_inc_ref(v_e_1920_);
v___x_1972_ = lean_apply_1(v_p_1917_, v_e_1920_);
v___x_1973_ = lean_unbox(v___x_1972_);
if (v___x_1973_ == 0)
{
v___y_1940_ = v_a_1921_;
v___y_1941_ = v___y_1922_;
v___y_1942_ = v___y_1923_;
v___y_1943_ = v___y_1924_;
v___y_1944_ = v___y_1925_;
v___y_1945_ = v___y_1926_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_1974_; 
lean_inc_ref(v_e_1920_);
v___x_1974_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4___redArg(v_e_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; uint8_t v___x_1976_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1976_ = lean_unbox(v_a_1975_);
lean_dec(v_a_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_inc_ref(v_f_1918_);
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
lean_inc(v___y_1922_);
lean_inc_ref(v_e_1920_);
v___x_1977_ = lean_apply_7(v_f_1918_, v_e_1920_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, lean_box(0));
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1985_; 
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1985_ == 0)
{
lean_object* v_unused_1986_; 
v_unused_1986_ = lean_ctor_get(v___x_1977_, 0);
lean_dec(v_unused_1986_);
v___x_1979_ = v___x_1977_;
v_isShared_1980_ = v_isSharedCheck_1985_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v___x_1977_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1985_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
if (v_stopWhenVisited_1919_ == 0)
{
lean_del_object(v___x_1979_);
v___y_1940_ = v_a_1921_;
v___y_1941_ = v___y_1922_;
v___y_1942_ = v___y_1923_;
v___y_1943_ = v___y_1924_;
v___y_1944_ = v___y_1925_;
v___y_1945_ = v___y_1926_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_f_1918_);
lean_dec_ref(v_p_1917_);
v___x_1981_ = lean_box(0);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1981_);
v___x_1983_ = v___x_1979_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_f_1918_);
lean_dec_ref(v_p_1917_);
return v___x_1977_;
}
}
else
{
v___y_1940_ = v_a_1921_;
v___y_1941_ = v___y_1922_;
v___y_1942_ = v___y_1923_;
v___y_1943_ = v___y_1924_;
v___y_1944_ = v___y_1925_;
v___y_1945_ = v___y_1926_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_f_1918_);
lean_dec_ref(v_p_1917_);
v_a_1987_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1974_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1974_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_f_1918_);
lean_dec_ref(v_p_1917_);
v___x_1995_ = lean_box(0);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1995_);
v___x_1997_ = v___x_1969_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
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
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_f_1918_);
lean_dec_ref(v_p_1917_);
v_a_2000_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1966_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1966_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
v___jp_1928_:
{
lean_object* v___x_1937_; 
lean_inc_ref(v_f_1918_);
lean_inc_ref(v_p_1917_);
v___x_1937_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2(v_p_1917_, v_f_1918_, v_stopWhenVisited_1919_, v_d_1934_, v___y_1936_, v___y_1930_, v___y_1929_, v___y_1931_, v___y_1933_, v___y_1932_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_dec_ref_known(v___x_1937_, 1);
v_e_1920_ = v_b_1935_;
v_a_1921_ = v___y_1936_;
v___y_1922_ = v___y_1930_;
v___y_1923_ = v___y_1929_;
v___y_1924_ = v___y_1931_;
v___y_1925_ = v___y_1933_;
v___y_1926_ = v___y_1932_;
goto _start;
}
else
{
lean_dec_ref(v_b_1935_);
lean_dec_ref(v_f_1918_);
lean_dec_ref(v_p_1917_);
return v___x_1937_;
}
}
v___jp_1939_:
{
switch(lean_obj_tag(v_e_1920_))
{
case 7:
{
lean_object* v_binderType_1946_; lean_object* v_body_1947_; 
v_binderType_1946_ = lean_ctor_get(v_e_1920_, 1);
lean_inc_ref(v_binderType_1946_);
v_body_1947_ = lean_ctor_get(v_e_1920_, 2);
lean_inc_ref(v_body_1947_);
lean_dec_ref_known(v_e_1920_, 3);
v___y_1929_ = v___y_1942_;
v___y_1930_ = v___y_1941_;
v___y_1931_ = v___y_1943_;
v___y_1932_ = v___y_1945_;
v___y_1933_ = v___y_1944_;
v_d_1934_ = v_binderType_1946_;
v_b_1935_ = v_body_1947_;
v___y_1936_ = v___y_1940_;
goto v___jp_1928_;
}
case 6:
{
lean_object* v_binderType_1948_; lean_object* v_body_1949_; 
v_binderType_1948_ = lean_ctor_get(v_e_1920_, 1);
lean_inc_ref(v_binderType_1948_);
v_body_1949_ = lean_ctor_get(v_e_1920_, 2);
lean_inc_ref(v_body_1949_);
lean_dec_ref_known(v_e_1920_, 3);
v___y_1929_ = v___y_1942_;
v___y_1930_ = v___y_1941_;
v___y_1931_ = v___y_1943_;
v___y_1932_ = v___y_1945_;
v___y_1933_ = v___y_1944_;
v_d_1934_ = v_binderType_1948_;
v_b_1935_ = v_body_1949_;
v___y_1936_ = v___y_1940_;
goto v___jp_1928_;
}
case 8:
{
lean_object* v_type_1950_; lean_object* v_value_1951_; lean_object* v_body_1952_; lean_object* v___x_1953_; 
v_type_1950_ = lean_ctor_get(v_e_1920_, 1);
lean_inc_ref(v_type_1950_);
v_value_1951_ = lean_ctor_get(v_e_1920_, 2);
lean_inc_ref(v_value_1951_);
v_body_1952_ = lean_ctor_get(v_e_1920_, 3);
lean_inc_ref(v_body_1952_);
lean_dec_ref_known(v_e_1920_, 4);
lean_inc_ref(v_f_1918_);
lean_inc_ref(v_p_1917_);
v___x_1953_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2(v_p_1917_, v_f_1918_, v_stopWhenVisited_1919_, v_type_1950_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v___x_1954_; 
lean_dec_ref_known(v___x_1953_, 1);
lean_inc_ref(v_f_1918_);
lean_inc_ref(v_p_1917_);
v___x_1954_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2(v_p_1917_, v_f_1918_, v_stopWhenVisited_1919_, v_value_1951_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_dec_ref_known(v___x_1954_, 1);
v_e_1920_ = v_body_1952_;
v_a_1921_ = v___y_1940_;
v___y_1922_ = v___y_1941_;
v___y_1923_ = v___y_1942_;
v___y_1924_ = v___y_1943_;
v___y_1925_ = v___y_1944_;
v___y_1926_ = v___y_1945_;
goto _start;
}
else
{
lean_dec_ref(v_body_1952_);
lean_dec_ref(v_f_1918_);
lean_dec_ref(v_p_1917_);
return v___x_1954_;
}
}
else
{
lean_dec_ref(v_body_1952_);
lean_dec_ref(v_value_1951_);
lean_dec_ref(v_f_1918_);
lean_dec_ref(v_p_1917_);
return v___x_1953_;
}
}
case 5:
{
lean_object* v_fn_1956_; lean_object* v_arg_1957_; lean_object* v___x_1958_; 
v_fn_1956_ = lean_ctor_get(v_e_1920_, 0);
lean_inc_ref(v_fn_1956_);
v_arg_1957_ = lean_ctor_get(v_e_1920_, 1);
lean_inc_ref(v_arg_1957_);
lean_dec_ref_known(v_e_1920_, 2);
lean_inc_ref(v_f_1918_);
lean_inc_ref(v_p_1917_);
v___x_1958_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2(v_p_1917_, v_f_1918_, v_stopWhenVisited_1919_, v_fn_1956_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_dec_ref_known(v___x_1958_, 1);
v_e_1920_ = v_arg_1957_;
v_a_1921_ = v___y_1940_;
v___y_1922_ = v___y_1941_;
v___y_1923_ = v___y_1942_;
v___y_1924_ = v___y_1943_;
v___y_1925_ = v___y_1944_;
v___y_1926_ = v___y_1945_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1957_);
lean_dec_ref(v_f_1918_);
lean_dec_ref(v_p_1917_);
return v___x_1958_;
}
}
case 10:
{
lean_object* v_expr_1960_; 
v_expr_1960_ = lean_ctor_get(v_e_1920_, 1);
lean_inc_ref(v_expr_1960_);
lean_dec_ref_known(v_e_1920_, 2);
v_e_1920_ = v_expr_1960_;
v_a_1921_ = v___y_1940_;
v___y_1922_ = v___y_1941_;
v___y_1923_ = v___y_1942_;
v___y_1924_ = v___y_1943_;
v___y_1925_ = v___y_1944_;
v___y_1926_ = v___y_1945_;
goto _start;
}
case 11:
{
lean_object* v_struct_1962_; 
v_struct_1962_ = lean_ctor_get(v_e_1920_, 2);
lean_inc_ref(v_struct_1962_);
lean_dec_ref_known(v_e_1920_, 3);
v_e_1920_ = v_struct_1962_;
v_a_1921_ = v___y_1940_;
v___y_1922_ = v___y_1941_;
v___y_1923_ = v___y_1942_;
v___y_1924_ = v___y_1943_;
v___y_1925_ = v___y_1944_;
v___y_1926_ = v___y_1945_;
goto _start;
}
default: 
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_f_1918_);
lean_dec_ref(v_p_1917_);
v___x_1964_ = lean_box(0);
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
return v___x_1965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2___boxed(lean_object* v_p_2008_, lean_object* v_f_2009_, lean_object* v_stopWhenVisited_2010_, lean_object* v_e_2011_, lean_object* v_a_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
uint8_t v_stopWhenVisited_boxed_2019_; lean_object* v_res_2020_; 
v_stopWhenVisited_boxed_2019_ = lean_unbox(v_stopWhenVisited_2010_);
v_res_2020_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2(v_p_2008_, v_f_2009_, v_stopWhenVisited_boxed_2019_, v_e_2011_, v_a_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec(v_a_2012_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object* v_p_2021_, lean_object* v_f_2022_, lean_object* v_e_2023_, uint8_t v_stopWhenVisited_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = l_Lean_ForEachExprWhere_initCache;
v___x_2032_ = lean_st_mk_ref(v___x_2031_);
v___x_2033_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2(v_p_2021_, v_f_2022_, v_stopWhenVisited_2024_, v_e_2023_, v___x_2032_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2042_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_st_ref_get(v___x_2032_);
lean_dec(v___x_2032_);
lean_dec(v___x_2038_);
if (v_isShared_2037_ == 0)
{
v___x_2040_ = v___x_2036_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2034_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
lean_dec(v___x_2032_);
return v___x_2033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object* v_p_2043_, lean_object* v_f_2044_, lean_object* v_e_2045_, lean_object* v_stopWhenVisited_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
uint8_t v_stopWhenVisited_boxed_2053_; lean_object* v_res_2054_; 
v_stopWhenVisited_boxed_2053_ = lean_unbox(v_stopWhenVisited_2046_);
v_res_2054_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_2043_, v_f_2044_, v_e_2045_, v_stopWhenVisited_boxed_2053_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(lean_object* v___f_2056_, lean_object* v___f_2057_, uint8_t v___x_2058_, lean_object* v_e_2059_, lean_object* v_candidates_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_2059_, v___y_2062_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2068_; lean_object* v___y_2070_; uint8_t v___x_2080_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2068_ = lean_st_mk_ref(v_candidates_2060_);
v___x_2080_ = l_Lean_Expr_hasFVar(v_a_2067_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec(v_a_2067_);
lean_dec_ref(v___f_2057_);
v___x_2081_ = lean_box(0);
lean_inc(v___y_2064_);
lean_inc_ref(v___y_2063_);
lean_inc(v___y_2062_);
lean_inc_ref(v___y_2061_);
lean_inc(v___x_2068_);
v___x_2082_ = lean_apply_7(v___f_2056_, v___x_2081_, v___x_2068_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, lean_box(0));
v___y_2070_ = v___x_2082_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2___closed__0));
v___x_2084_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2083_, v___f_2057_, v_a_2067_, v___x_2058_, v___x_2068_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
lean_inc(v___y_2064_);
lean_inc_ref(v___y_2063_);
lean_inc(v___y_2062_);
lean_inc_ref(v___y_2061_);
lean_inc(v___x_2068_);
v___x_2086_ = lean_apply_7(v___f_2056_, v_a_2085_, v___x_2068_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, lean_box(0));
v___y_2070_ = v___x_2086_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v___x_2068_);
lean_dec_ref(v___f_2056_);
v_a_2087_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2084_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2084_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
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
v___jp_2069_:
{
if (lean_obj_tag(v___y_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2079_; 
v_a_2071_ = lean_ctor_get(v___y_2070_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___y_2070_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2073_ = v___y_2070_;
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___y_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = lean_st_ref_get(v___x_2068_);
lean_dec(v___x_2068_);
lean_dec(v___x_2075_);
if (v_isShared_2074_ == 0)
{
v___x_2077_ = v___x_2073_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2071_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
else
{
lean_dec(v___x_2068_);
return v___y_2070_;
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v_candidates_2060_);
lean_dec_ref(v___f_2057_);
lean_dec_ref(v___f_2056_);
v_a_2095_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2066_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2066_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2___boxed(lean_object* v___f_2103_, lean_object* v___f_2104_, lean_object* v___x_2105_, lean_object* v_e_2106_, lean_object* v_candidates_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
uint8_t v___x_21355__boxed_2113_; lean_object* v_res_2114_; 
v___x_21355__boxed_2113_ = lean_unbox(v___x_2105_);
v_res_2114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(v___f_2103_, v___f_2104_, v___x_21355__boxed_2113_, v_e_2106_, v_candidates_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__0(lean_object* v_____r_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_st_ref_get(v___y_2116_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__0___boxed(lean_object* v_____r_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__0(v_____r_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__1(lean_object* v_e_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2139_ = lean_st_ref_take(v___y_2133_);
v___x_2140_ = l_Lean_Expr_fvarId_x21(v_e_2132_);
v___x_2141_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_2139_, v___x_2140_);
lean_dec(v___x_2140_);
v___x_2142_ = lean_st_ref_put(v___y_2133_, v___x_2141_);
v___x_2143_ = lean_box(0);
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__1___boxed(lean_object* v_e_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__1(v_e_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v_e_2145_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9___redArg(lean_object* v_b_2153_, lean_object* v_acc_2154_, lean_object* v_i_2155_){
_start:
{
lean_object* v___y_2157_; lean_object* v_keyArray_2165_; lean_object* v_valueArray_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v_keyArray_2165_ = lean_ctor_get(v_b_2153_, 1);
v_valueArray_2166_ = lean_ctor_get(v_b_2153_, 2);
v___x_2167_ = lean_array_get_size(v_keyArray_2165_);
v___x_2168_ = lean_nat_dec_lt(v_i_2155_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_dec(v_i_2155_);
return v_acc_2154_;
}
else
{
lean_object* v___x_2169_; uint8_t v_isSome_2170_; 
v___x_2169_ = lean_array_fget_borrowed(v_keyArray_2165_, v_i_2155_);
v_isSome_2170_ = lean_noption_is_some(v___x_2169_);
if (v_isSome_2170_ == 0)
{
goto v___jp_2161_;
}
else
{
lean_object* v___x_2171_; uint8_t v_isSome_2172_; 
v___x_2171_ = lean_array_fget_borrowed(v_valueArray_2166_, v_i_2155_);
v_isSome_2172_ = lean_noption_is_some(v___x_2171_);
if (v_isSome_2172_ == 0)
{
goto v___jp_2161_;
}
else
{
lean_object* v_val_2173_; lean_object* v_val_2174_; lean_object* v_i_2176_; lean_object* v___x_2181_; 
lean_inc(v___x_2169_);
v_val_2173_ = lean_noption_get(v___x_2169_);
lean_inc(v___x_2171_);
v_val_2174_ = lean_noption_get(v___x_2171_);
v___x_2181_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_acc_2154_, v_val_2173_);
switch(lean_obj_tag(v___x_2181_))
{
case 0:
{
lean_object* v_index_2182_; lean_object* v_size_2183_; lean_object* v___x_2184_; 
v_index_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_index_2182_);
lean_dec_ref_known(v___x_2181_, 3);
v_size_2183_ = lean_ctor_get(v_acc_2154_, 0);
lean_inc(v_size_2183_);
v___x_2184_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2154_, v_size_2183_, v_index_2182_, v_val_2173_, v_val_2174_);
lean_dec(v_index_2182_);
v___y_2157_ = v___x_2184_;
goto v___jp_2156_;
}
case 1:
{
lean_object* v_index_2185_; 
v_index_2185_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_index_2185_);
lean_dec_ref_known(v___x_2181_, 1);
v_i_2176_ = v_index_2185_;
goto v___jp_2175_;
}
default: 
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2154_, v___x_2186_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_index_2188_; 
v_index_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_index_2188_);
lean_dec_ref_known(v___x_2187_, 1);
v_i_2176_ = v_index_2188_;
goto v___jp_2175_;
}
else
{
lean_dec(v_val_2174_);
lean_dec(v_val_2173_);
v___y_2157_ = v_acc_2154_;
goto v___jp_2156_;
}
}
}
v___jp_2175_:
{
lean_object* v_size_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v_size_2177_ = lean_ctor_get(v_acc_2154_, 0);
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_add(v_size_2177_, v___x_2178_);
v___x_2180_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2154_, v___x_2179_, v_i_2176_, v_val_2173_, v_val_2174_);
lean_dec(v_i_2176_);
v___y_2157_ = v___x_2180_;
goto v___jp_2156_;
}
}
}
}
v___jp_2156_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = lean_nat_add(v_i_2155_, v___x_2158_);
lean_dec(v_i_2155_);
v_acc_2154_ = v___y_2157_;
v_i_2155_ = v___x_2159_;
goto _start;
}
v___jp_2161_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_unsigned_to_nat(1u);
v___x_2163_ = lean_nat_add(v_i_2155_, v___x_2162_);
lean_dec(v_i_2155_);
v_i_2155_ = v___x_2163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_b_2189_, lean_object* v_acc_2190_, lean_object* v_i_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9___redArg(v_b_2189_, v_acc_2190_, v_i_2191_);
lean_dec_ref(v_b_2189_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6___redArg(lean_object* v_init_2193_, lean_object* v_b_2194_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9___redArg(v_b_2194_, v_init_2193_, v___x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6___redArg___boxed(lean_object* v_init_2197_, lean_object* v_b_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6___redArg(v_init_2197_, v_b_2198_);
lean_dec_ref(v_b_2198_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(lean_object* v_m_2200_){
_start:
{
lean_object* v_keyArray_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_cellCount_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_target_2208_; lean_object* v___x_2209_; 
v_keyArray_2201_ = lean_ctor_get(v_m_2200_, 1);
v___x_2202_ = lean_array_get_size(v_keyArray_2201_);
v___x_2203_ = lean_unsigned_to_nat(2u);
v_cellCount_2204_ = lean_nat_mul(v___x_2202_, v___x_2203_);
v___x_2205_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2204_);
v___x_2206_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2204_);
v___x_2207_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2204_);
v_target_2208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2208_, 0, v___x_2205_);
lean_ctor_set(v_target_2208_, 1, v___x_2206_);
lean_ctor_set(v_target_2208_, 2, v___x_2207_);
v___x_2209_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6___redArg(v_target_2208_, v_m_2200_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg___boxed(lean_object* v_m_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v_m_2210_);
lean_dec_ref(v_m_2210_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19(lean_object* v_as_2214_, size_t v_sz_2215_, size_t v_i_2216_, lean_object* v_b_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
uint8_t v___x_2223_; 
v___x_2223_ = lean_usize_dec_lt(v_i_2216_, v_sz_2215_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_b_2217_);
return v___x_2224_;
}
else
{
lean_object* v_snd_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2358_; 
v_snd_2225_ = lean_ctor_get(v_b_2217_, 1);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_b_2217_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v_b_2217_, 0);
lean_dec(v_unused_2359_);
v___x_2227_ = v_b_2217_;
v_isShared_2228_ = v_isSharedCheck_2358_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_snd_2225_);
lean_dec(v_b_2217_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2358_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v_a_2231_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v_i_2242_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v_i_2263_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v_a_2281_; 
v___x_2229_ = lean_box(0);
v_a_2281_ = lean_array_uget_borrowed(v_as_2214_, v_i_2216_);
if (lean_obj_tag(v_a_2281_) == 0)
{
v_a_2231_ = v_snd_2225_;
goto v___jp_2230_;
}
else
{
lean_object* v_val_2282_; lean_object* v___y_2284_; uint8_t v___x_2314_; 
v_val_2282_ = lean_ctor_get(v_a_2281_, 0);
v___x_2314_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2282_);
if (v___x_2314_ == 0)
{
lean_object* v___f_2315_; lean_object* v___f_2316_; lean_object* v___x_2317_; lean_object* v_candidates_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___x_2336_; 
v___f_2315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__0));
v___f_2316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__1));
v___x_2317_ = l_Lean_LocalDecl_type(v_val_2282_);
lean_inc_ref(v___x_2317_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(v___f_2315_, v___f_2316_, v___x_2314_, v___x_2317_, v_snd_2225_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2338_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = l_Lean_LocalDecl_value_x3f(v_val_2282_, v___x_2314_);
if (lean_obj_tag(v___x_2338_) == 0)
{
v_candidates_2319_ = v_a_2337_;
v___y_2320_ = v___y_2218_;
v___y_2321_ = v___y_2219_;
v___y_2322_ = v___y_2220_;
v___y_2323_ = v___y_2221_;
goto v___jp_2318_;
}
else
{
lean_object* v_val_2339_; lean_object* v___x_2340_; 
v_val_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_val_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(v___f_2315_, v___f_2316_, v___x_2314_, v_val_2339_, v_a_2337_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v_candidates_2319_ = v_a_2341_;
v___y_2320_ = v___y_2218_;
v___y_2321_ = v___y_2219_;
v___y_2322_ = v___y_2220_;
v___y_2323_ = v___y_2221_;
goto v___jp_2318_;
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref(v___x_2317_);
lean_del_object(v___x_2227_);
v_a_2342_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2340_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2340_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v___x_2317_);
lean_del_object(v___x_2227_);
v_a_2350_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2336_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2336_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
v___jp_2318_:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Meta_isProp(v___x_2317_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; uint8_t v___x_2326_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = lean_unbox(v_a_2325_);
lean_dec(v_a_2325_);
if (v___x_2326_ == 0)
{
v_a_2231_ = v_candidates_2319_;
goto v___jp_2230_;
}
else
{
uint8_t v___x_2327_; 
v___x_2327_ = l_Lean_LocalDecl_hasValue(v_val_2282_, v___x_2314_);
if (v___x_2327_ == 0)
{
v___y_2284_ = v_candidates_2319_;
goto v___jp_2283_;
}
else
{
if (v___x_2314_ == 0)
{
v_a_2231_ = v_candidates_2319_;
goto v___jp_2230_;
}
else
{
v___y_2284_ = v_candidates_2319_;
goto v___jp_2283_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec_ref(v_candidates_2319_);
lean_del_object(v___x_2227_);
v_a_2328_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2324_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2324_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
else
{
v_a_2231_ = v_snd_2225_;
goto v___jp_2230_;
}
v___jp_2283_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = l_Lean_LocalDecl_fvarId(v_val_2282_);
v___x_2286_ = lean_box(0);
v___x_2287_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2284_, v___x_2285_);
switch(lean_obj_tag(v___x_2287_))
{
case 0:
{
lean_dec_ref_known(v___x_2287_, 3);
lean_dec(v___x_2285_);
v_a_2231_ = v___y_2284_;
goto v___jp_2230_;
}
case 1:
{
lean_object* v_index_2288_; lean_object* v_size_2289_; lean_object* v_keyArray_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v_index_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_index_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v_size_2289_ = lean_ctor_get(v___y_2284_, 0);
v_keyArray_2290_ = lean_ctor_get(v___y_2284_, 1);
v___x_2291_ = lean_unsigned_to_nat(1u);
v___x_2292_ = lean_nat_add(v_size_2289_, v___x_2291_);
v___x_2293_ = lean_array_get_size(v_keyArray_2290_);
v___x_2294_ = lean_nat_dec_lt(v___x_2292_, v___x_2293_);
if (v___x_2294_ == 0)
{
lean_dec(v___x_2292_);
lean_dec(v_index_2288_);
v___y_2269_ = v___y_2284_;
v___y_2270_ = v___x_2286_;
v___y_2271_ = v___x_2285_;
goto v___jp_2268_;
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2295_ = lean_unsigned_to_nat(4u);
v___x_2296_ = lean_nat_mul(v___x_2292_, v___x_2295_);
v___x_2297_ = lean_unsigned_to_nat(3u);
v___x_2298_ = lean_nat_mul(v___x_2293_, v___x_2297_);
v___x_2299_ = lean_nat_dec_le(v___x_2296_, v___x_2298_);
lean_dec(v___x_2298_);
lean_dec(v___x_2296_);
if (v___x_2299_ == 0)
{
lean_dec(v___x_2292_);
lean_dec(v_index_2288_);
v___y_2269_ = v___y_2284_;
v___y_2270_ = v___x_2286_;
v___y_2271_ = v___x_2285_;
goto v___jp_2268_;
}
else
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2284_, v___x_2292_, v_index_2288_, v___x_2285_, v___x_2286_);
lean_dec(v_index_2288_);
v_a_2231_ = v___x_2300_;
goto v___jp_2230_;
}
}
}
default: 
{
lean_object* v_size_2301_; lean_object* v_keyArray_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v_size_2301_ = lean_ctor_get(v___y_2284_, 0);
v_keyArray_2302_ = lean_ctor_get(v___y_2284_, 1);
v___x_2303_ = lean_unsigned_to_nat(1u);
v___x_2304_ = lean_nat_add(v_size_2301_, v___x_2303_);
v___x_2305_ = lean_array_get_size(v_keyArray_2302_);
v___x_2306_ = lean_nat_dec_lt(v___x_2304_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; 
lean_dec(v___x_2304_);
v___x_2307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2284_);
lean_dec_ref(v___y_2284_);
v___y_2248_ = v___x_2286_;
v___y_2249_ = v___x_2285_;
v___y_2250_ = v___x_2307_;
goto v___jp_2247_;
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2308_ = lean_unsigned_to_nat(4u);
v___x_2309_ = lean_nat_mul(v___x_2304_, v___x_2308_);
lean_dec(v___x_2304_);
v___x_2310_ = lean_unsigned_to_nat(3u);
v___x_2311_ = lean_nat_mul(v___x_2305_, v___x_2310_);
v___x_2312_ = lean_nat_dec_le(v___x_2309_, v___x_2311_);
lean_dec(v___x_2311_);
lean_dec(v___x_2309_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2284_);
lean_dec_ref(v___y_2284_);
v___y_2248_ = v___x_2286_;
v___y_2249_ = v___x_2285_;
v___y_2250_ = v___x_2313_;
goto v___jp_2247_;
}
else
{
v___y_2248_ = v___x_2286_;
v___y_2249_ = v___x_2285_;
v___y_2250_ = v___y_2284_;
goto v___jp_2247_;
}
}
}
}
}
}
v___jp_2230_:
{
lean_object* v___x_2233_; 
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v_a_2231_);
lean_ctor_set(v___x_2227_, 0, v___x_2229_);
v___x_2233_ = v___x_2227_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_a_2231_);
v___x_2233_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
size_t v___x_2234_; size_t v___x_2235_; 
v___x_2234_ = ((size_t)1ULL);
v___x_2235_ = lean_usize_add(v_i_2216_, v___x_2234_);
v_i_2216_ = v___x_2235_;
v_b_2217_ = v___x_2233_;
goto _start;
}
}
v___jp_2238_:
{
lean_object* v_size_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_size_2243_ = lean_ctor_get(v___y_2241_, 0);
v___x_2244_ = lean_unsigned_to_nat(1u);
v___x_2245_ = lean_nat_add(v_size_2243_, v___x_2244_);
v___x_2246_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2241_, v___x_2245_, v_i_2242_, v___y_2240_, v___y_2239_);
lean_dec(v_i_2242_);
v_a_2231_ = v___x_2246_;
goto v___jp_2230_;
}
v___jp_2247_:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2250_, v___y_2249_);
switch(lean_obj_tag(v___x_2251_))
{
case 0:
{
lean_object* v_index_2252_; lean_object* v_size_2253_; lean_object* v___x_2254_; 
v_index_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_index_2252_);
lean_dec_ref_known(v___x_2251_, 3);
v_size_2253_ = lean_ctor_get(v___y_2250_, 0);
lean_inc(v_size_2253_);
v___x_2254_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2250_, v_size_2253_, v_index_2252_, v___y_2249_, v___y_2248_);
lean_dec(v_index_2252_);
v_a_2231_ = v___x_2254_;
goto v___jp_2230_;
}
case 1:
{
lean_object* v_index_2255_; 
v_index_2255_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_index_2255_);
lean_dec_ref_known(v___x_2251_, 1);
v___y_2239_ = v___y_2248_;
v___y_2240_ = v___y_2249_;
v___y_2241_ = v___y_2250_;
v_i_2242_ = v_index_2255_;
goto v___jp_2238_;
}
default: 
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_unsigned_to_nat(0u);
v___x_2257_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2250_, v___x_2256_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_index_2258_; 
v_index_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_index_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v___y_2239_ = v___y_2248_;
v___y_2240_ = v___y_2249_;
v___y_2241_ = v___y_2250_;
v_i_2242_ = v_index_2258_;
goto v___jp_2238_;
}
else
{
lean_dec(v___y_2249_);
v_a_2231_ = v___y_2250_;
goto v___jp_2230_;
}
}
}
}
v___jp_2259_:
{
lean_object* v_size_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_size_2264_ = lean_ctor_get(v___y_2261_, 0);
v___x_2265_ = lean_unsigned_to_nat(1u);
v___x_2266_ = lean_nat_add(v_size_2264_, v___x_2265_);
v___x_2267_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2261_, v___x_2266_, v_i_2263_, v___y_2262_, v___y_2260_);
lean_dec(v_i_2263_);
v_a_2231_ = v___x_2267_;
goto v___jp_2230_;
}
v___jp_2268_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2269_);
lean_dec_ref(v___y_2269_);
v___x_2273_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___x_2272_, v___y_2271_);
switch(lean_obj_tag(v___x_2273_))
{
case 0:
{
lean_object* v_index_2274_; lean_object* v_size_2275_; lean_object* v___x_2276_; 
v_index_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_index_2274_);
lean_dec_ref_known(v___x_2273_, 3);
v_size_2275_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_size_2275_);
v___x_2276_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2272_, v_size_2275_, v_index_2274_, v___y_2271_, v___y_2270_);
lean_dec(v_index_2274_);
v_a_2231_ = v___x_2276_;
goto v___jp_2230_;
}
case 1:
{
lean_object* v_index_2277_; 
v_index_2277_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_index_2277_);
lean_dec_ref_known(v___x_2273_, 1);
v___y_2260_ = v___y_2270_;
v___y_2261_ = v___x_2272_;
v___y_2262_ = v___y_2271_;
v_i_2263_ = v_index_2277_;
goto v___jp_2259_;
}
default: 
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2272_, v___x_2278_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_index_2280_; 
v_index_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_index_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___y_2260_ = v___y_2270_;
v___y_2261_ = v___x_2272_;
v___y_2262_ = v___y_2271_;
v_i_2263_ = v_index_2280_;
goto v___jp_2259_;
}
else
{
lean_dec(v___y_2271_);
v_a_2231_ = v___x_2272_;
goto v___jp_2230_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___boxed(lean_object* v_as_2360_, lean_object* v_sz_2361_, lean_object* v_i_2362_, lean_object* v_b_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
size_t v_sz_boxed_2369_; size_t v_i_boxed_2370_; lean_object* v_res_2371_; 
v_sz_boxed_2369_ = lean_unbox_usize(v_sz_2361_);
lean_dec(v_sz_2361_);
v_i_boxed_2370_ = lean_unbox_usize(v_i_2362_);
lean_dec(v_i_2362_);
v_res_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19(v_as_2360_, v_sz_boxed_2369_, v_i_boxed_2370_, v_b_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec_ref(v_as_2360_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13(lean_object* v_as_2372_, size_t v_sz_2373_, size_t v_i_2374_, lean_object* v_b_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
uint8_t v___x_2381_; 
v___x_2381_ = lean_usize_dec_lt(v_i_2374_, v_sz_2373_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v_b_2375_);
return v___x_2382_;
}
else
{
lean_object* v_snd_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2516_; 
v_snd_2383_ = lean_ctor_get(v_b_2375_, 1);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_b_2375_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v_b_2375_, 0);
lean_dec(v_unused_2517_);
v___x_2385_ = v_b_2375_;
v_isShared_2386_ = v_isSharedCheck_2516_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_snd_2383_);
lean_dec(v_b_2375_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2516_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v_a_2389_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v_i_2400_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v_i_2421_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v_a_2439_; 
v___x_2387_ = lean_box(0);
v_a_2439_ = lean_array_uget_borrowed(v_as_2372_, v_i_2374_);
if (lean_obj_tag(v_a_2439_) == 0)
{
v_a_2389_ = v_snd_2383_;
goto v___jp_2388_;
}
else
{
lean_object* v_val_2440_; lean_object* v___y_2442_; uint8_t v___x_2472_; 
v_val_2440_ = lean_ctor_get(v_a_2439_, 0);
v___x_2472_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2440_);
if (v___x_2472_ == 0)
{
lean_object* v___f_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v_candidates_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___x_2494_; 
v___f_2473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__0));
v___f_2474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__1));
v___x_2475_ = l_Lean_LocalDecl_type(v_val_2440_);
lean_inc_ref(v___x_2475_);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(v___f_2473_, v___f_2474_, v___x_2472_, v___x_2475_, v_snd_2383_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2496_ = l_Lean_LocalDecl_value_x3f(v_val_2440_, v___x_2472_);
if (lean_obj_tag(v___x_2496_) == 0)
{
v_candidates_2477_ = v_a_2495_;
v___y_2478_ = v___y_2376_;
v___y_2479_ = v___y_2377_;
v___y_2480_ = v___y_2378_;
v___y_2481_ = v___y_2379_;
goto v___jp_2476_;
}
else
{
lean_object* v_val_2497_; lean_object* v___x_2498_; 
v_val_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_val_2497_);
lean_dec_ref_known(v___x_2496_, 1);
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(v___f_2473_, v___f_2474_, v___x_2472_, v_val_2497_, v_a_2495_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v_candidates_2477_ = v_a_2499_;
v___y_2478_ = v___y_2376_;
v___y_2479_ = v___y_2377_;
v___y_2480_ = v___y_2378_;
v___y_2481_ = v___y_2379_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec_ref(v___x_2475_);
lean_del_object(v___x_2385_);
v_a_2500_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2498_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2498_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec_ref(v___x_2475_);
lean_del_object(v___x_2385_);
v_a_2508_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2494_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2494_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
v___jp_2476_:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Meta_isProp(v___x_2475_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; uint8_t v___x_2484_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
v___x_2484_ = lean_unbox(v_a_2483_);
lean_dec(v_a_2483_);
if (v___x_2484_ == 0)
{
v_a_2389_ = v_candidates_2477_;
goto v___jp_2388_;
}
else
{
uint8_t v___x_2485_; 
v___x_2485_ = l_Lean_LocalDecl_hasValue(v_val_2440_, v___x_2472_);
if (v___x_2485_ == 0)
{
v___y_2442_ = v_candidates_2477_;
goto v___jp_2441_;
}
else
{
if (v___x_2472_ == 0)
{
v_a_2389_ = v_candidates_2477_;
goto v___jp_2388_;
}
else
{
v___y_2442_ = v_candidates_2477_;
goto v___jp_2441_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec_ref(v_candidates_2477_);
lean_del_object(v___x_2385_);
v_a_2486_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2482_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2482_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
else
{
v_a_2389_ = v_snd_2383_;
goto v___jp_2388_;
}
v___jp_2441_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2443_ = l_Lean_LocalDecl_fvarId(v_val_2440_);
v___x_2444_ = lean_box(0);
v___x_2445_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2442_, v___x_2443_);
switch(lean_obj_tag(v___x_2445_))
{
case 0:
{
lean_dec_ref_known(v___x_2445_, 3);
lean_dec(v___x_2443_);
v_a_2389_ = v___y_2442_;
goto v___jp_2388_;
}
case 1:
{
lean_object* v_index_2446_; lean_object* v_size_2447_; lean_object* v_keyArray_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v_index_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_index_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v_size_2447_ = lean_ctor_get(v___y_2442_, 0);
v_keyArray_2448_ = lean_ctor_get(v___y_2442_, 1);
v___x_2449_ = lean_unsigned_to_nat(1u);
v___x_2450_ = lean_nat_add(v_size_2447_, v___x_2449_);
v___x_2451_ = lean_array_get_size(v_keyArray_2448_);
v___x_2452_ = lean_nat_dec_lt(v___x_2450_, v___x_2451_);
if (v___x_2452_ == 0)
{
lean_dec(v___x_2450_);
lean_dec(v_index_2446_);
v___y_2427_ = v___x_2444_;
v___y_2428_ = v___y_2442_;
v___y_2429_ = v___x_2443_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2453_ = lean_unsigned_to_nat(4u);
v___x_2454_ = lean_nat_mul(v___x_2450_, v___x_2453_);
v___x_2455_ = lean_unsigned_to_nat(3u);
v___x_2456_ = lean_nat_mul(v___x_2451_, v___x_2455_);
v___x_2457_ = lean_nat_dec_le(v___x_2454_, v___x_2456_);
lean_dec(v___x_2456_);
lean_dec(v___x_2454_);
if (v___x_2457_ == 0)
{
lean_dec(v___x_2450_);
lean_dec(v_index_2446_);
v___y_2427_ = v___x_2444_;
v___y_2428_ = v___y_2442_;
v___y_2429_ = v___x_2443_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2442_, v___x_2450_, v_index_2446_, v___x_2443_, v___x_2444_);
lean_dec(v_index_2446_);
v_a_2389_ = v___x_2458_;
goto v___jp_2388_;
}
}
}
default: 
{
lean_object* v_size_2459_; lean_object* v_keyArray_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v_size_2459_ = lean_ctor_get(v___y_2442_, 0);
v_keyArray_2460_ = lean_ctor_get(v___y_2442_, 1);
v___x_2461_ = lean_unsigned_to_nat(1u);
v___x_2462_ = lean_nat_add(v_size_2459_, v___x_2461_);
v___x_2463_ = lean_array_get_size(v_keyArray_2460_);
v___x_2464_ = lean_nat_dec_lt(v___x_2462_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; 
lean_dec(v___x_2462_);
v___x_2465_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2442_);
lean_dec_ref(v___y_2442_);
v___y_2406_ = v___x_2444_;
v___y_2407_ = v___x_2443_;
v___y_2408_ = v___x_2465_;
goto v___jp_2405_;
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2466_ = lean_unsigned_to_nat(4u);
v___x_2467_ = lean_nat_mul(v___x_2462_, v___x_2466_);
lean_dec(v___x_2462_);
v___x_2468_ = lean_unsigned_to_nat(3u);
v___x_2469_ = lean_nat_mul(v___x_2463_, v___x_2468_);
v___x_2470_ = lean_nat_dec_le(v___x_2467_, v___x_2469_);
lean_dec(v___x_2469_);
lean_dec(v___x_2467_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2442_);
lean_dec_ref(v___y_2442_);
v___y_2406_ = v___x_2444_;
v___y_2407_ = v___x_2443_;
v___y_2408_ = v___x_2471_;
goto v___jp_2405_;
}
else
{
v___y_2406_ = v___x_2444_;
v___y_2407_ = v___x_2443_;
v___y_2408_ = v___y_2442_;
goto v___jp_2405_;
}
}
}
}
}
}
v___jp_2388_:
{
lean_object* v___x_2391_; 
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 1, v_a_2389_);
lean_ctor_set(v___x_2385_, 0, v___x_2387_);
v___x_2391_ = v___x_2385_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_a_2389_);
v___x_2391_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
size_t v___x_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = ((size_t)1ULL);
v___x_2393_ = lean_usize_add(v_i_2374_, v___x_2392_);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19(v_as_2372_, v_sz_2373_, v___x_2393_, v___x_2391_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2394_;
}
}
v___jp_2396_:
{
lean_object* v_size_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_size_2401_ = lean_ctor_get(v___y_2399_, 0);
v___x_2402_ = lean_unsigned_to_nat(1u);
v___x_2403_ = lean_nat_add(v_size_2401_, v___x_2402_);
v___x_2404_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2399_, v___x_2403_, v_i_2400_, v___y_2398_, v___y_2397_);
lean_dec(v_i_2400_);
v_a_2389_ = v___x_2404_;
goto v___jp_2388_;
}
v___jp_2405_:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2408_, v___y_2407_);
switch(lean_obj_tag(v___x_2409_))
{
case 0:
{
lean_object* v_index_2410_; lean_object* v_size_2411_; lean_object* v___x_2412_; 
v_index_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_index_2410_);
lean_dec_ref_known(v___x_2409_, 3);
v_size_2411_ = lean_ctor_get(v___y_2408_, 0);
lean_inc(v_size_2411_);
v___x_2412_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2408_, v_size_2411_, v_index_2410_, v___y_2407_, v___y_2406_);
lean_dec(v_index_2410_);
v_a_2389_ = v___x_2412_;
goto v___jp_2388_;
}
case 1:
{
lean_object* v_index_2413_; 
v_index_2413_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_index_2413_);
lean_dec_ref_known(v___x_2409_, 1);
v___y_2397_ = v___y_2406_;
v___y_2398_ = v___y_2407_;
v___y_2399_ = v___y_2408_;
v_i_2400_ = v_index_2413_;
goto v___jp_2396_;
}
default: 
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2408_, v___x_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_index_2416_; 
v_index_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_index_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___y_2397_ = v___y_2406_;
v___y_2398_ = v___y_2407_;
v___y_2399_ = v___y_2408_;
v_i_2400_ = v_index_2416_;
goto v___jp_2396_;
}
else
{
lean_dec(v___y_2407_);
v_a_2389_ = v___y_2408_;
goto v___jp_2388_;
}
}
}
}
v___jp_2417_:
{
lean_object* v_size_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_size_2422_ = lean_ctor_get(v___y_2419_, 0);
v___x_2423_ = lean_unsigned_to_nat(1u);
v___x_2424_ = lean_nat_add(v_size_2422_, v___x_2423_);
v___x_2425_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2419_, v___x_2424_, v_i_2421_, v___y_2420_, v___y_2418_);
lean_dec(v_i_2421_);
v_a_2389_ = v___x_2425_;
goto v___jp_2388_;
}
v___jp_2426_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2428_);
lean_dec_ref(v___y_2428_);
v___x_2431_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___x_2430_, v___y_2429_);
switch(lean_obj_tag(v___x_2431_))
{
case 0:
{
lean_object* v_index_2432_; lean_object* v_size_2433_; lean_object* v___x_2434_; 
v_index_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_index_2432_);
lean_dec_ref_known(v___x_2431_, 3);
v_size_2433_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_size_2433_);
v___x_2434_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2430_, v_size_2433_, v_index_2432_, v___y_2429_, v___y_2427_);
lean_dec(v_index_2432_);
v_a_2389_ = v___x_2434_;
goto v___jp_2388_;
}
case 1:
{
lean_object* v_index_2435_; 
v_index_2435_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_index_2435_);
lean_dec_ref_known(v___x_2431_, 1);
v___y_2418_ = v___y_2427_;
v___y_2419_ = v___x_2430_;
v___y_2420_ = v___y_2429_;
v_i_2421_ = v_index_2435_;
goto v___jp_2417_;
}
default: 
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2430_, v___x_2436_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_index_2438_; 
v_index_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_index_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___y_2418_ = v___y_2427_;
v___y_2419_ = v___x_2430_;
v___y_2420_ = v___y_2429_;
v_i_2421_ = v_index_2438_;
goto v___jp_2417_;
}
else
{
lean_dec(v___y_2429_);
v_a_2389_ = v___x_2430_;
goto v___jp_2388_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13___boxed(lean_object* v_as_2518_, lean_object* v_sz_2519_, lean_object* v_i_2520_, lean_object* v_b_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
size_t v_sz_boxed_2527_; size_t v_i_boxed_2528_; lean_object* v_res_2529_; 
v_sz_boxed_2527_ = lean_unbox_usize(v_sz_2519_);
lean_dec(v_sz_2519_);
v_i_boxed_2528_ = lean_unbox_usize(v_i_2520_);
lean_dec(v_i_2520_);
v_res_2529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13(v_as_2518_, v_sz_boxed_2527_, v_i_boxed_2528_, v_b_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec_ref(v_as_2518_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8(lean_object* v_init_2530_, lean_object* v_n_2531_, lean_object* v_b_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
if (lean_obj_tag(v_n_2531_) == 0)
{
lean_object* v_cs_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; size_t v_sz_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v_cs_2538_ = lean_ctor_get(v_n_2531_, 0);
v___x_2539_ = lean_box(0);
v___x_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
lean_ctor_set(v___x_2540_, 1, v_b_2532_);
v_sz_2541_ = lean_array_size(v_cs_2538_);
v___x_2542_ = ((size_t)0ULL);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__12(v_init_2530_, v_cs_2538_, v_sz_2541_, v___x_2542_, v___x_2540_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2558_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2558_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2558_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v_fst_2548_; 
v_fst_2548_ = lean_ctor_get(v_a_2544_, 0);
if (lean_obj_tag(v_fst_2548_) == 0)
{
lean_object* v_snd_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; 
v_snd_2549_ = lean_ctor_get(v_a_2544_, 1);
lean_inc(v_snd_2549_);
lean_dec(v_a_2544_);
v___x_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_snd_2549_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2550_);
v___x_2552_ = v___x_2546_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
else
{
lean_object* v_val_2554_; lean_object* v___x_2556_; 
lean_inc_ref(v_fst_2548_);
lean_dec(v_a_2544_);
v_val_2554_ = lean_ctor_get(v_fst_2548_, 0);
lean_inc(v_val_2554_);
lean_dec_ref_known(v_fst_2548_, 1);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v_val_2554_);
v___x_2556_ = v___x_2546_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_val_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_a_2559_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2543_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2543_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v_vs_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; size_t v_sz_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v_vs_2567_ = lean_ctor_get(v_n_2531_, 0);
v___x_2568_ = lean_box(0);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
lean_ctor_set(v___x_2569_, 1, v_b_2532_);
v_sz_2570_ = lean_array_size(v_vs_2567_);
v___x_2571_ = ((size_t)0ULL);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13(v_vs_2567_, v_sz_2570_, v___x_2571_, v___x_2569_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2587_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2587_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2587_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v_fst_2577_; 
v_fst_2577_ = lean_ctor_get(v_a_2573_, 0);
if (lean_obj_tag(v_fst_2577_) == 0)
{
lean_object* v_snd_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
v_snd_2578_ = lean_ctor_get(v_a_2573_, 1);
lean_inc(v_snd_2578_);
lean_dec(v_a_2573_);
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_snd_2578_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2579_);
v___x_2581_ = v___x_2575_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
else
{
lean_object* v_val_2583_; lean_object* v___x_2585_; 
lean_inc_ref(v_fst_2577_);
lean_dec(v_a_2573_);
v_val_2583_ = lean_ctor_get(v_fst_2577_, 0);
lean_inc(v_val_2583_);
lean_dec_ref_known(v_fst_2577_, 1);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v_val_2583_);
v___x_2585_ = v___x_2575_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_val_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
v_a_2588_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2572_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2572_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__12(lean_object* v_init_2596_, lean_object* v_as_2597_, size_t v_sz_2598_, size_t v_i_2599_, lean_object* v_b_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
uint8_t v___x_2606_; 
v___x_2606_ = lean_usize_dec_lt(v_i_2599_, v_sz_2598_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v_b_2600_);
return v___x_2607_;
}
else
{
lean_object* v_snd_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2642_; 
v_snd_2608_ = lean_ctor_get(v_b_2600_, 1);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_b_2600_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; 
v_unused_2643_ = lean_ctor_get(v_b_2600_, 0);
lean_dec(v_unused_2643_);
v___x_2610_ = v_b_2600_;
v_isShared_2611_ = v_isSharedCheck_2642_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_snd_2608_);
lean_dec(v_b_2600_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2642_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v_a_2612_; lean_object* v___x_2613_; 
v_a_2612_ = lean_array_uget_borrowed(v_as_2597_, v_i_2599_);
lean_inc(v_snd_2608_);
v___x_2613_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8(v_init_2596_, v_a_2612_, v_snd_2608_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2633_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2633_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2633_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
if (lean_obj_tag(v_a_2614_) == 0)
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v_a_2614_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2618_);
v___x_2620_ = v___x_2610_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_snd_2608_);
v___x_2620_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2622_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2620_);
v___x_2622_ = v___x_2616_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
lean_del_object(v___x_2616_);
lean_dec(v_snd_2608_);
v_a_2625_ = lean_ctor_get(v_a_2614_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v_a_2614_, 1);
v___x_2626_ = lean_box(0);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 1, v_a_2625_);
lean_ctor_set(v___x_2610_, 0, v___x_2626_);
v___x_2628_ = v___x_2610_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v_a_2625_);
v___x_2628_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
size_t v___x_2629_; size_t v___x_2630_; 
v___x_2629_ = ((size_t)1ULL);
v___x_2630_ = lean_usize_add(v_i_2599_, v___x_2629_);
v_i_2599_ = v___x_2630_;
v_b_2600_ = v___x_2628_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_del_object(v___x_2610_);
lean_dec(v_snd_2608_);
v_a_2634_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2613_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2613_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__12___boxed(lean_object* v_init_2644_, lean_object* v_as_2645_, lean_object* v_sz_2646_, lean_object* v_i_2647_, lean_object* v_b_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
size_t v_sz_boxed_2654_; size_t v_i_boxed_2655_; lean_object* v_res_2656_; 
v_sz_boxed_2654_ = lean_unbox_usize(v_sz_2646_);
lean_dec(v_sz_2646_);
v_i_boxed_2655_ = lean_unbox_usize(v_i_2647_);
lean_dec(v_i_2647_);
v_res_2656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__12(v_init_2644_, v_as_2645_, v_sz_boxed_2654_, v_i_boxed_2655_, v_b_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v_as_2645_);
lean_dec_ref(v_init_2644_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8___boxed(lean_object* v_init_2657_, lean_object* v_n_2658_, lean_object* v_b_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8(v_init_2657_, v_n_2658_, v_b_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec_ref(v_n_2658_);
lean_dec_ref(v_init_2657_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9_spec__15(lean_object* v_as_2666_, size_t v_sz_2667_, size_t v_i_2668_, lean_object* v_b_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
uint8_t v___x_2675_; 
v___x_2675_ = lean_usize_dec_lt(v_i_2668_, v_sz_2667_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v_b_2669_);
return v___x_2676_;
}
else
{
lean_object* v_snd_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2810_; 
v_snd_2677_ = lean_ctor_get(v_b_2669_, 1);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_b_2669_);
if (v_isSharedCheck_2810_ == 0)
{
lean_object* v_unused_2811_; 
v_unused_2811_ = lean_ctor_get(v_b_2669_, 0);
lean_dec(v_unused_2811_);
v___x_2679_ = v_b_2669_;
v_isShared_2680_ = v_isSharedCheck_2810_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_snd_2677_);
lean_dec(v_b_2669_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2810_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; lean_object* v_a_2683_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v_i_2694_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v_i_2715_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v_a_2733_; 
v___x_2681_ = lean_box(0);
v_a_2733_ = lean_array_uget_borrowed(v_as_2666_, v_i_2668_);
if (lean_obj_tag(v_a_2733_) == 0)
{
v_a_2683_ = v_snd_2677_;
goto v___jp_2682_;
}
else
{
lean_object* v_val_2734_; lean_object* v___y_2736_; uint8_t v___x_2766_; 
v_val_2734_ = lean_ctor_get(v_a_2733_, 0);
v___x_2766_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2734_);
if (v___x_2766_ == 0)
{
lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v_candidates_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___x_2788_; 
v___f_2767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__0));
v___f_2768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__1));
v___x_2769_ = l_Lean_LocalDecl_type(v_val_2734_);
lean_inc_ref(v___x_2769_);
v___x_2788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(v___f_2767_, v___f_2768_, v___x_2766_, v___x_2769_, v_snd_2677_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = l_Lean_LocalDecl_value_x3f(v_val_2734_, v___x_2766_);
if (lean_obj_tag(v___x_2790_) == 0)
{
v_candidates_2771_ = v_a_2789_;
v___y_2772_ = v___y_2670_;
v___y_2773_ = v___y_2671_;
v___y_2774_ = v___y_2672_;
v___y_2775_ = v___y_2673_;
goto v___jp_2770_;
}
else
{
lean_object* v_val_2791_; lean_object* v___x_2792_; 
v_val_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_val_2791_);
lean_dec_ref_known(v___x_2790_, 1);
v___x_2792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(v___f_2767_, v___f_2768_, v___x_2766_, v_val_2791_, v_a_2789_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v_candidates_2771_ = v_a_2793_;
v___y_2772_ = v___y_2670_;
v___y_2773_ = v___y_2671_;
v___y_2774_ = v___y_2672_;
v___y_2775_ = v___y_2673_;
goto v___jp_2770_;
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref(v___x_2769_);
lean_del_object(v___x_2679_);
v_a_2794_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2792_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2792_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec_ref(v___x_2769_);
lean_del_object(v___x_2679_);
v_a_2802_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2788_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2788_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
v___jp_2770_:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Meta_isProp(v___x_2769_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; uint8_t v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = lean_unbox(v_a_2777_);
lean_dec(v_a_2777_);
if (v___x_2778_ == 0)
{
v_a_2683_ = v_candidates_2771_;
goto v___jp_2682_;
}
else
{
uint8_t v___x_2779_; 
v___x_2779_ = l_Lean_LocalDecl_hasValue(v_val_2734_, v___x_2766_);
if (v___x_2779_ == 0)
{
v___y_2736_ = v_candidates_2771_;
goto v___jp_2735_;
}
else
{
if (v___x_2766_ == 0)
{
v_a_2683_ = v_candidates_2771_;
goto v___jp_2682_;
}
else
{
v___y_2736_ = v_candidates_2771_;
goto v___jp_2735_;
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec_ref(v_candidates_2771_);
lean_del_object(v___x_2679_);
v_a_2780_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2776_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2776_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
else
{
v_a_2683_ = v_snd_2677_;
goto v___jp_2682_;
}
v___jp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = l_Lean_LocalDecl_fvarId(v_val_2734_);
v___x_2738_ = lean_box(0);
v___x_2739_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2736_, v___x_2737_);
switch(lean_obj_tag(v___x_2739_))
{
case 0:
{
lean_dec_ref_known(v___x_2739_, 3);
lean_dec(v___x_2737_);
v_a_2683_ = v___y_2736_;
goto v___jp_2682_;
}
case 1:
{
lean_object* v_index_2740_; lean_object* v_size_2741_; lean_object* v_keyArray_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; 
v_index_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_index_2740_);
lean_dec_ref_known(v___x_2739_, 1);
v_size_2741_ = lean_ctor_get(v___y_2736_, 0);
v_keyArray_2742_ = lean_ctor_get(v___y_2736_, 1);
v___x_2743_ = lean_unsigned_to_nat(1u);
v___x_2744_ = lean_nat_add(v_size_2741_, v___x_2743_);
v___x_2745_ = lean_array_get_size(v_keyArray_2742_);
v___x_2746_ = lean_nat_dec_lt(v___x_2744_, v___x_2745_);
if (v___x_2746_ == 0)
{
lean_dec(v___x_2744_);
lean_dec(v_index_2740_);
v___y_2721_ = v___y_2736_;
v___y_2722_ = v___x_2737_;
v___y_2723_ = v___x_2738_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2747_ = lean_unsigned_to_nat(4u);
v___x_2748_ = lean_nat_mul(v___x_2744_, v___x_2747_);
v___x_2749_ = lean_unsigned_to_nat(3u);
v___x_2750_ = lean_nat_mul(v___x_2745_, v___x_2749_);
v___x_2751_ = lean_nat_dec_le(v___x_2748_, v___x_2750_);
lean_dec(v___x_2750_);
lean_dec(v___x_2748_);
if (v___x_2751_ == 0)
{
lean_dec(v___x_2744_);
lean_dec(v_index_2740_);
v___y_2721_ = v___y_2736_;
v___y_2722_ = v___x_2737_;
v___y_2723_ = v___x_2738_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2736_, v___x_2744_, v_index_2740_, v___x_2737_, v___x_2738_);
lean_dec(v_index_2740_);
v_a_2683_ = v___x_2752_;
goto v___jp_2682_;
}
}
}
default: 
{
lean_object* v_size_2753_; lean_object* v_keyArray_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v_size_2753_ = lean_ctor_get(v___y_2736_, 0);
v_keyArray_2754_ = lean_ctor_get(v___y_2736_, 1);
v___x_2755_ = lean_unsigned_to_nat(1u);
v___x_2756_ = lean_nat_add(v_size_2753_, v___x_2755_);
v___x_2757_ = lean_array_get_size(v_keyArray_2754_);
v___x_2758_ = lean_nat_dec_lt(v___x_2756_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; 
lean_dec(v___x_2756_);
v___x_2759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2736_);
lean_dec_ref(v___y_2736_);
v___y_2700_ = v___x_2737_;
v___y_2701_ = v___x_2738_;
v___y_2702_ = v___x_2759_;
goto v___jp_2699_;
}
else
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2760_ = lean_unsigned_to_nat(4u);
v___x_2761_ = lean_nat_mul(v___x_2756_, v___x_2760_);
lean_dec(v___x_2756_);
v___x_2762_ = lean_unsigned_to_nat(3u);
v___x_2763_ = lean_nat_mul(v___x_2757_, v___x_2762_);
v___x_2764_ = lean_nat_dec_le(v___x_2761_, v___x_2763_);
lean_dec(v___x_2763_);
lean_dec(v___x_2761_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2736_);
lean_dec_ref(v___y_2736_);
v___y_2700_ = v___x_2737_;
v___y_2701_ = v___x_2738_;
v___y_2702_ = v___x_2765_;
goto v___jp_2699_;
}
else
{
v___y_2700_ = v___x_2737_;
v___y_2701_ = v___x_2738_;
v___y_2702_ = v___y_2736_;
goto v___jp_2699_;
}
}
}
}
}
}
v___jp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 1, v_a_2683_);
lean_ctor_set(v___x_2679_, 0, v___x_2681_);
v___x_2685_ = v___x_2679_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_a_2683_);
v___x_2685_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
size_t v___x_2686_; size_t v___x_2687_; 
v___x_2686_ = ((size_t)1ULL);
v___x_2687_ = lean_usize_add(v_i_2668_, v___x_2686_);
v_i_2668_ = v___x_2687_;
v_b_2669_ = v___x_2685_;
goto _start;
}
}
v___jp_2690_:
{
lean_object* v_size_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_size_2695_ = lean_ctor_get(v___y_2692_, 0);
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_add(v_size_2695_, v___x_2696_);
v___x_2698_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2692_, v___x_2697_, v_i_2694_, v___y_2691_, v___y_2693_);
lean_dec(v_i_2694_);
v_a_2683_ = v___x_2698_;
goto v___jp_2682_;
}
v___jp_2699_:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2702_, v___y_2700_);
switch(lean_obj_tag(v___x_2703_))
{
case 0:
{
lean_object* v_index_2704_; lean_object* v_size_2705_; lean_object* v___x_2706_; 
v_index_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_index_2704_);
lean_dec_ref_known(v___x_2703_, 3);
v_size_2705_ = lean_ctor_get(v___y_2702_, 0);
lean_inc(v_size_2705_);
v___x_2706_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2702_, v_size_2705_, v_index_2704_, v___y_2700_, v___y_2701_);
lean_dec(v_index_2704_);
v_a_2683_ = v___x_2706_;
goto v___jp_2682_;
}
case 1:
{
lean_object* v_index_2707_; 
v_index_2707_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_index_2707_);
lean_dec_ref_known(v___x_2703_, 1);
v___y_2691_ = v___y_2700_;
v___y_2692_ = v___y_2702_;
v___y_2693_ = v___y_2701_;
v_i_2694_ = v_index_2707_;
goto v___jp_2690_;
}
default: 
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = lean_unsigned_to_nat(0u);
v___x_2709_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2702_, v___x_2708_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_index_2710_; 
v_index_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_index_2710_);
lean_dec_ref_known(v___x_2709_, 1);
v___y_2691_ = v___y_2700_;
v___y_2692_ = v___y_2702_;
v___y_2693_ = v___y_2701_;
v_i_2694_ = v_index_2710_;
goto v___jp_2690_;
}
else
{
lean_dec(v___y_2700_);
v_a_2683_ = v___y_2702_;
goto v___jp_2682_;
}
}
}
}
v___jp_2711_:
{
lean_object* v_size_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_size_2716_ = lean_ctor_get(v___y_2713_, 0);
v___x_2717_ = lean_unsigned_to_nat(1u);
v___x_2718_ = lean_nat_add(v_size_2716_, v___x_2717_);
v___x_2719_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2713_, v___x_2718_, v_i_2715_, v___y_2712_, v___y_2714_);
lean_dec(v_i_2715_);
v_a_2683_ = v___x_2719_;
goto v___jp_2682_;
}
v___jp_2720_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2721_);
lean_dec_ref(v___y_2721_);
v___x_2725_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___x_2724_, v___y_2722_);
switch(lean_obj_tag(v___x_2725_))
{
case 0:
{
lean_object* v_index_2726_; lean_object* v_size_2727_; lean_object* v___x_2728_; 
v_index_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_index_2726_);
lean_dec_ref_known(v___x_2725_, 3);
v_size_2727_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_size_2727_);
v___x_2728_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2724_, v_size_2727_, v_index_2726_, v___y_2722_, v___y_2723_);
lean_dec(v_index_2726_);
v_a_2683_ = v___x_2728_;
goto v___jp_2682_;
}
case 1:
{
lean_object* v_index_2729_; 
v_index_2729_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_index_2729_);
lean_dec_ref_known(v___x_2725_, 1);
v___y_2712_ = v___y_2722_;
v___y_2713_ = v___x_2724_;
v___y_2714_ = v___y_2723_;
v_i_2715_ = v_index_2729_;
goto v___jp_2711_;
}
default: 
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = lean_unsigned_to_nat(0u);
v___x_2731_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2724_, v___x_2730_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_index_2732_; 
v_index_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_index_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___y_2712_ = v___y_2722_;
v___y_2713_ = v___x_2724_;
v___y_2714_ = v___y_2723_;
v_i_2715_ = v_index_2732_;
goto v___jp_2711_;
}
else
{
lean_dec(v___y_2722_);
v_a_2683_ = v___x_2724_;
goto v___jp_2682_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9_spec__15___boxed(lean_object* v_as_2812_, lean_object* v_sz_2813_, lean_object* v_i_2814_, lean_object* v_b_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
size_t v_sz_boxed_2821_; size_t v_i_boxed_2822_; lean_object* v_res_2823_; 
v_sz_boxed_2821_ = lean_unbox_usize(v_sz_2813_);
lean_dec(v_sz_2813_);
v_i_boxed_2822_ = lean_unbox_usize(v_i_2814_);
lean_dec(v_i_2814_);
v_res_2823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9_spec__15(v_as_2812_, v_sz_boxed_2821_, v_i_boxed_2822_, v_b_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec_ref(v_as_2812_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9(lean_object* v_as_2824_, size_t v_sz_2825_, size_t v_i_2826_, lean_object* v_b_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_usize_dec_lt(v_i_2826_, v_sz_2825_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; 
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_b_2827_);
return v___x_2834_;
}
else
{
lean_object* v_snd_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2968_; 
v_snd_2835_ = lean_ctor_get(v_b_2827_, 1);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_b_2827_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v_b_2827_, 0);
lean_dec(v_unused_2969_);
v___x_2837_ = v_b_2827_;
v_isShared_2838_ = v_isSharedCheck_2968_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_snd_2835_);
lean_dec(v_b_2827_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2968_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v_a_2841_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v_i_2852_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v_i_2873_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v_a_2891_; 
v___x_2839_ = lean_box(0);
v_a_2891_ = lean_array_uget_borrowed(v_as_2824_, v_i_2826_);
if (lean_obj_tag(v_a_2891_) == 0)
{
v_a_2841_ = v_snd_2835_;
goto v___jp_2840_;
}
else
{
lean_object* v_val_2892_; lean_object* v___y_2894_; uint8_t v___x_2924_; 
v_val_2892_ = lean_ctor_get(v_a_2891_, 0);
v___x_2924_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2892_);
if (v___x_2924_ == 0)
{
lean_object* v___f_2925_; lean_object* v___f_2926_; lean_object* v___x_2927_; lean_object* v_candidates_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___x_2946_; 
v___f_2925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__0));
v___f_2926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8_spec__13_spec__19___closed__1));
v___x_2927_ = l_Lean_LocalDecl_type(v_val_2892_);
lean_inc_ref(v___x_2927_);
v___x_2946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(v___f_2925_, v___f_2926_, v___x_2924_, v___x_2927_, v_snd_2835_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2948_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v___x_2948_ = l_Lean_LocalDecl_value_x3f(v_val_2892_, v___x_2924_);
if (lean_obj_tag(v___x_2948_) == 0)
{
v_candidates_2929_ = v_a_2947_;
v___y_2930_ = v___y_2828_;
v___y_2931_ = v___y_2829_;
v___y_2932_ = v___y_2830_;
v___y_2933_ = v___y_2831_;
goto v___jp_2928_;
}
else
{
lean_object* v_val_2949_; lean_object* v___x_2950_; 
v_val_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_val_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2(v___f_2925_, v___f_2926_, v___x_2924_, v_val_2949_, v_a_2947_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
v_candidates_2929_ = v_a_2951_;
v___y_2930_ = v___y_2828_;
v___y_2931_ = v___y_2829_;
v___y_2932_ = v___y_2830_;
v___y_2933_ = v___y_2831_;
goto v___jp_2928_;
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec_ref(v___x_2927_);
lean_del_object(v___x_2837_);
v_a_2952_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2950_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2950_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v___x_2927_);
lean_del_object(v___x_2837_);
v_a_2960_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2946_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2946_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
v___jp_2928_:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_Meta_isProp(v___x_2927_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; uint8_t v___x_2936_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = lean_unbox(v_a_2935_);
lean_dec(v_a_2935_);
if (v___x_2936_ == 0)
{
v_a_2841_ = v_candidates_2929_;
goto v___jp_2840_;
}
else
{
uint8_t v___x_2937_; 
v___x_2937_ = l_Lean_LocalDecl_hasValue(v_val_2892_, v___x_2924_);
if (v___x_2937_ == 0)
{
v___y_2894_ = v_candidates_2929_;
goto v___jp_2893_;
}
else
{
if (v___x_2924_ == 0)
{
v_a_2841_ = v_candidates_2929_;
goto v___jp_2840_;
}
else
{
v___y_2894_ = v_candidates_2929_;
goto v___jp_2893_;
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec_ref(v_candidates_2929_);
lean_del_object(v___x_2837_);
v_a_2938_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2934_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2934_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
}
else
{
v_a_2841_ = v_snd_2835_;
goto v___jp_2840_;
}
v___jp_2893_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2895_ = l_Lean_LocalDecl_fvarId(v_val_2892_);
v___x_2896_ = lean_box(0);
v___x_2897_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2894_, v___x_2895_);
switch(lean_obj_tag(v___x_2897_))
{
case 0:
{
lean_dec_ref_known(v___x_2897_, 3);
lean_dec(v___x_2895_);
v_a_2841_ = v___y_2894_;
goto v___jp_2840_;
}
case 1:
{
lean_object* v_index_2898_; lean_object* v_size_2899_; lean_object* v_keyArray_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; 
v_index_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_index_2898_);
lean_dec_ref_known(v___x_2897_, 1);
v_size_2899_ = lean_ctor_get(v___y_2894_, 0);
v_keyArray_2900_ = lean_ctor_get(v___y_2894_, 1);
v___x_2901_ = lean_unsigned_to_nat(1u);
v___x_2902_ = lean_nat_add(v_size_2899_, v___x_2901_);
v___x_2903_ = lean_array_get_size(v_keyArray_2900_);
v___x_2904_ = lean_nat_dec_lt(v___x_2902_, v___x_2903_);
if (v___x_2904_ == 0)
{
lean_dec(v___x_2902_);
lean_dec(v_index_2898_);
v___y_2879_ = v___y_2894_;
v___y_2880_ = v___x_2895_;
v___y_2881_ = v___x_2896_;
goto v___jp_2878_;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2905_ = lean_unsigned_to_nat(4u);
v___x_2906_ = lean_nat_mul(v___x_2902_, v___x_2905_);
v___x_2907_ = lean_unsigned_to_nat(3u);
v___x_2908_ = lean_nat_mul(v___x_2903_, v___x_2907_);
v___x_2909_ = lean_nat_dec_le(v___x_2906_, v___x_2908_);
lean_dec(v___x_2908_);
lean_dec(v___x_2906_);
if (v___x_2909_ == 0)
{
lean_dec(v___x_2902_);
lean_dec(v_index_2898_);
v___y_2879_ = v___y_2894_;
v___y_2880_ = v___x_2895_;
v___y_2881_ = v___x_2896_;
goto v___jp_2878_;
}
else
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2894_, v___x_2902_, v_index_2898_, v___x_2895_, v___x_2896_);
lean_dec(v_index_2898_);
v_a_2841_ = v___x_2910_;
goto v___jp_2840_;
}
}
}
default: 
{
lean_object* v_size_2911_; lean_object* v_keyArray_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v_size_2911_ = lean_ctor_get(v___y_2894_, 0);
v_keyArray_2912_ = lean_ctor_get(v___y_2894_, 1);
v___x_2913_ = lean_unsigned_to_nat(1u);
v___x_2914_ = lean_nat_add(v_size_2911_, v___x_2913_);
v___x_2915_ = lean_array_get_size(v_keyArray_2912_);
v___x_2916_ = lean_nat_dec_lt(v___x_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; 
lean_dec(v___x_2914_);
v___x_2917_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2894_);
lean_dec_ref(v___y_2894_);
v___y_2858_ = v___x_2895_;
v___y_2859_ = v___x_2896_;
v___y_2860_ = v___x_2917_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; 
v___x_2918_ = lean_unsigned_to_nat(4u);
v___x_2919_ = lean_nat_mul(v___x_2914_, v___x_2918_);
lean_dec(v___x_2914_);
v___x_2920_ = lean_unsigned_to_nat(3u);
v___x_2921_ = lean_nat_mul(v___x_2915_, v___x_2920_);
v___x_2922_ = lean_nat_dec_le(v___x_2919_, v___x_2921_);
lean_dec(v___x_2921_);
lean_dec(v___x_2919_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2894_);
lean_dec_ref(v___y_2894_);
v___y_2858_ = v___x_2895_;
v___y_2859_ = v___x_2896_;
v___y_2860_ = v___x_2923_;
goto v___jp_2857_;
}
else
{
v___y_2858_ = v___x_2895_;
v___y_2859_ = v___x_2896_;
v___y_2860_ = v___y_2894_;
goto v___jp_2857_;
}
}
}
}
}
}
v___jp_2840_:
{
lean_object* v___x_2843_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v_a_2841_);
lean_ctor_set(v___x_2837_, 0, v___x_2839_);
v___x_2843_ = v___x_2837_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_a_2841_);
v___x_2843_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
size_t v___x_2844_; size_t v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = ((size_t)1ULL);
v___x_2845_ = lean_usize_add(v_i_2826_, v___x_2844_);
v___x_2846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9_spec__15(v_as_2824_, v_sz_2825_, v___x_2845_, v___x_2843_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2846_;
}
}
v___jp_2848_:
{
lean_object* v_size_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v_size_2853_ = lean_ctor_get(v___y_2851_, 0);
v___x_2854_ = lean_unsigned_to_nat(1u);
v___x_2855_ = lean_nat_add(v_size_2853_, v___x_2854_);
v___x_2856_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2851_, v___x_2855_, v_i_2852_, v___y_2849_, v___y_2850_);
lean_dec(v_i_2852_);
v_a_2841_ = v___x_2856_;
goto v___jp_2840_;
}
v___jp_2857_:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2860_, v___y_2858_);
switch(lean_obj_tag(v___x_2861_))
{
case 0:
{
lean_object* v_index_2862_; lean_object* v_size_2863_; lean_object* v___x_2864_; 
v_index_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_index_2862_);
lean_dec_ref_known(v___x_2861_, 3);
v_size_2863_ = lean_ctor_get(v___y_2860_, 0);
lean_inc(v_size_2863_);
v___x_2864_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2860_, v_size_2863_, v_index_2862_, v___y_2858_, v___y_2859_);
lean_dec(v_index_2862_);
v_a_2841_ = v___x_2864_;
goto v___jp_2840_;
}
case 1:
{
lean_object* v_index_2865_; 
v_index_2865_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_index_2865_);
lean_dec_ref_known(v___x_2861_, 1);
v___y_2849_ = v___y_2858_;
v___y_2850_ = v___y_2859_;
v___y_2851_ = v___y_2860_;
v_i_2852_ = v_index_2865_;
goto v___jp_2848_;
}
default: 
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_unsigned_to_nat(0u);
v___x_2867_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2860_, v___x_2866_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_index_2868_; 
v_index_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_index_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___y_2849_ = v___y_2858_;
v___y_2850_ = v___y_2859_;
v___y_2851_ = v___y_2860_;
v_i_2852_ = v_index_2868_;
goto v___jp_2848_;
}
else
{
lean_dec(v___y_2858_);
v_a_2841_ = v___y_2860_;
goto v___jp_2840_;
}
}
}
}
v___jp_2869_:
{
lean_object* v_size_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_size_2874_ = lean_ctor_get(v___y_2872_, 0);
v___x_2875_ = lean_unsigned_to_nat(1u);
v___x_2876_ = lean_nat_add(v_size_2874_, v___x_2875_);
v___x_2877_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2872_, v___x_2876_, v_i_2873_, v___y_2870_, v___y_2871_);
lean_dec(v_i_2873_);
v_a_2841_ = v___x_2877_;
goto v___jp_2840_;
}
v___jp_2878_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v___y_2879_);
lean_dec_ref(v___y_2879_);
v___x_2883_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___x_2882_, v___y_2880_);
switch(lean_obj_tag(v___x_2883_))
{
case 0:
{
lean_object* v_index_2884_; lean_object* v_size_2885_; lean_object* v___x_2886_; 
v_index_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_index_2884_);
lean_dec_ref_known(v___x_2883_, 3);
v_size_2885_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_size_2885_);
v___x_2886_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2882_, v_size_2885_, v_index_2884_, v___y_2880_, v___y_2881_);
lean_dec(v_index_2884_);
v_a_2841_ = v___x_2886_;
goto v___jp_2840_;
}
case 1:
{
lean_object* v_index_2887_; 
v_index_2887_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_index_2887_);
lean_dec_ref_known(v___x_2883_, 1);
v___y_2870_ = v___y_2880_;
v___y_2871_ = v___y_2881_;
v___y_2872_ = v___x_2882_;
v_i_2873_ = v_index_2887_;
goto v___jp_2869_;
}
default: 
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_unsigned_to_nat(0u);
v___x_2889_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2882_, v___x_2888_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_index_2890_; 
v_index_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_index_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___y_2870_ = v___y_2880_;
v___y_2871_ = v___y_2881_;
v___y_2872_ = v___x_2882_;
v_i_2873_ = v_index_2890_;
goto v___jp_2869_;
}
else
{
lean_dec(v___y_2880_);
v_a_2841_ = v___x_2882_;
goto v___jp_2840_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___boxed(lean_object* v_as_2970_, lean_object* v_sz_2971_, lean_object* v_i_2972_, lean_object* v_b_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
size_t v_sz_boxed_2979_; size_t v_i_boxed_2980_; lean_object* v_res_2981_; 
v_sz_boxed_2979_ = lean_unbox_usize(v_sz_2971_);
lean_dec(v_sz_2971_);
v_i_boxed_2980_ = lean_unbox_usize(v_i_2972_);
lean_dec(v_i_2972_);
v_res_2981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9(v_as_2970_, v_sz_boxed_2979_, v_i_boxed_2980_, v_b_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec_ref(v_as_2970_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_t_2982_, lean_object* v_init_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v_root_2989_; lean_object* v_tail_2990_; lean_object* v___x_2991_; 
v_root_2989_ = lean_ctor_get(v_t_2982_, 0);
v_tail_2990_ = lean_ctor_get(v_t_2982_, 1);
lean_inc_ref(v_init_2983_);
v___x_2991_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__8(v_init_2983_, v_root_2989_, v_init_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec_ref(v_init_2983_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3028_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_2994_ = v___x_2991_;
v_isShared_2995_ = v_isSharedCheck_3028_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3028_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
if (lean_obj_tag(v_a_2992_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2998_; 
v_a_2996_ = lean_ctor_get(v_a_2992_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v_a_2992_, 1);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v_a_2996_);
v___x_2998_ = v___x_2994_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; size_t v_sz_3003_; size_t v___x_3004_; lean_object* v___x_3005_; 
lean_del_object(v___x_2994_);
v_a_3000_ = lean_ctor_get(v_a_2992_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v_a_2992_, 1);
v___x_3001_ = lean_box(0);
v___x_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set(v___x_3002_, 1, v_a_3000_);
v_sz_3003_ = lean_array_size(v_tail_2990_);
v___x_3004_ = ((size_t)0ULL);
v___x_3005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9(v_tail_2990_, v_sz_3003_, v___x_3004_, v___x_3002_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3019_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3008_ = v___x_3005_;
v_isShared_3009_ = v_isSharedCheck_3019_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3019_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v_fst_3010_; 
v_fst_3010_ = lean_ctor_get(v_a_3006_, 0);
if (lean_obj_tag(v_fst_3010_) == 0)
{
lean_object* v_snd_3011_; lean_object* v___x_3013_; 
v_snd_3011_ = lean_ctor_get(v_a_3006_, 1);
lean_inc(v_snd_3011_);
lean_dec(v_a_3006_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v_snd_3011_);
v___x_3013_ = v___x_3008_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_snd_3011_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
else
{
lean_object* v_val_3015_; lean_object* v___x_3017_; 
lean_inc_ref(v_fst_3010_);
lean_dec(v_a_3006_);
v_val_3015_ = lean_ctor_get(v_fst_3010_, 0);
lean_inc(v_val_3015_);
lean_dec_ref_known(v_fst_3010_, 1);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v_val_3015_);
v___x_3017_ = v___x_3008_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_val_3015_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
v_a_3020_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3005_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3005_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
v_a_3029_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_2991_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_2991_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_t_3037_, lean_object* v_init_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_t_3037_, v_init_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec_ref(v_t_3037_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_3047_, lean_object* v_mvarId_3048_, lean_object* v___f_3049_, lean_object* v___f_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v_lctx_3056_; lean_object* v_decls_3057_; lean_object* v___x_3058_; 
v_lctx_3056_ = lean_ctor_get(v___y_3051_, 2);
v_decls_3057_ = lean_ctor_get(v_lctx_3056_, 1);
lean_inc_ref(v_decls_3057_);
v___x_3058_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_decls_3057_, v_candidates_3047_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v___x_3060_ = l_Lean_MVarId_getType(v_mvarId_3048_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; lean_object* v_a_3063_; lean_object* v___x_3064_; lean_object* v___y_3066_; uint8_t v___x_3090_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3062_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_3061_, v___y_3052_);
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref(v___x_3062_);
v___x_3064_ = lean_st_mk_ref(v_a_3059_);
v___x_3090_ = l_Lean_Expr_hasFVar(v_a_3063_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_dec(v_a_3063_);
lean_dec_ref(v___f_3050_);
v___x_3091_ = lean_box(0);
lean_inc(v___y_3054_);
lean_inc_ref(v___y_3053_);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
lean_inc(v___x_3064_);
v___x_3092_ = lean_apply_7(v___f_3049_, v___x_3091_, v___x_3064_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, lean_box(0));
v___y_3066_ = v___x_3092_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3093_; uint8_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__4_spec__9___lam__2___closed__0));
v___x_3094_ = 0;
v___x_3095_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_3093_, v___f_3050_, v_a_3063_, v___x_3094_, v___x_3064_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
lean_inc(v___y_3054_);
lean_inc_ref(v___y_3053_);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
lean_inc(v___x_3064_);
v___x_3097_ = lean_apply_7(v___f_3049_, v_a_3096_, v___x_3064_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, lean_box(0));
v___y_3066_ = v___x_3097_;
goto v___jp_3065_;
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v___x_3064_);
lean_dec_ref(v_decls_3057_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v___f_3049_);
v_a_3098_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3095_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3095_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
v___jp_3065_:
{
if (lean_obj_tag(v___y_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3081_; 
v_a_3067_ = lean_ctor_get(v___y_3066_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___y_3066_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3069_ = v___y_3066_;
v_isShared_3070_ = v_isSharedCheck_3081_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___y_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3081_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v_size_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; 
v___x_3071_ = lean_st_ref_get(v___x_3064_);
lean_dec(v___x_3064_);
lean_dec(v___x_3071_);
v_size_3072_ = lean_ctor_get(v_a_3067_, 0);
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = lean_nat_dec_eq(v_size_3072_, v___x_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_del_object(v___x_3069_);
v___x_3075_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3076_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6(v_a_3067_, v_decls_3057_, v___x_3075_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v_decls_3057_);
lean_dec(v_a_3067_);
return v___x_3076_;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3079_; 
lean_dec(v_a_3067_);
lean_dec_ref(v_decls_3057_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
v___x_3077_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3077_);
v___x_3079_ = v___x_3069_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v___x_3064_);
lean_dec_ref(v_decls_3057_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
v_a_3082_ = lean_ctor_get(v___y_3066_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___y_3066_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___y_3066_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___y_3066_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_a_3059_);
lean_dec_ref(v_decls_3057_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v___f_3050_);
lean_dec_ref(v___f_3049_);
v_a_3106_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3060_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3060_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec_ref(v_decls_3057_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v___f_3050_);
lean_dec_ref(v___f_3049_);
lean_dec(v_mvarId_3048_);
v_a_3114_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3058_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3058_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_3122_, lean_object* v_mvarId_3123_, lean_object* v___f_3124_, lean_object* v___f_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_3122_, v_mvarId_3123_, v___f_3124_, v___f_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v___f_3140_; lean_object* v___f_3141_; lean_object* v_candidates_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; 
v___f_3140_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_3141_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_3142_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_3134_);
v___f_3143_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_3143_, 0, v_candidates_3142_);
lean_closure_set(v___f_3143_, 1, v_mvarId_3134_);
lean_closure_set(v___f_3143_, 2, v___f_3141_);
lean_closure_set(v___f_3143_, 3, v___f_3140_);
v___x_3144_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3134_, v___f_3143_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_3152_, lean_object* v_m_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_3153_, v_a_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_3156_, lean_object* v_m_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_3156_, v_m_3157_, v_a_3158_);
lean_dec(v_a_3158_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_3160_, lean_object* v_m_3161_, lean_object* v_query_3162_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_3161_, v_query_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2___boxed(lean_object* v_00_u03b2_3164_, lean_object* v_m_3165_, lean_object* v_query_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2(v_00_u03b2_3164_, v_m_3165_, v_query_3166_);
lean_dec(v_query_3166_);
lean_dec_ref(v_m_3165_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_00_u03b2_3168_, lean_object* v_m_3169_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___redArg(v_m_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_00_u03b2_3171_, lean_object* v_m_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_00_u03b2_3171_, v_m_3172_);
lean_dec_ref(v_m_3172_);
return v_res_3173_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_00_u03b2_3174_, lean_object* v_m_3175_, lean_object* v_a_3176_){
_start:
{
uint8_t v___x_3177_; 
v___x_3177_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___redArg(v_m_3175_, v_a_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_00_u03b2_3178_, lean_object* v_m_3179_, lean_object* v_a_3180_){
_start:
{
uint8_t v_res_3181_; lean_object* v_r_3182_; 
v_res_3181_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_00_u03b2_3178_, v_m_3179_, v_a_3180_);
lean_dec(v_a_3180_);
lean_dec_ref(v_m_3179_);
v_r_3182_ = lean_box(v_res_3181_);
return v_r_3182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_3183_, lean_object* v_m_3184_, lean_object* v_query_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_m_3184_, v_query_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3187_, lean_object* v_m_3188_, lean_object* v_query_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_3187_, v_m_3188_, v_query_3189_);
lean_dec(v_query_3189_);
lean_dec_ref(v_m_3188_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3(lean_object* v_e_3191_, lean_object* v_a_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3___redArg(v_e_3191_, v_a_3192_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3___boxed(lean_object* v_e_3200_, lean_object* v_a_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__3(v_e_3200_, v_a_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec(v_a_3201_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4(lean_object* v_00_u03b2_3209_, lean_object* v_m_3210_, lean_object* v_query_3211_, lean_object* v_x_3212_, lean_object* v_x_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4___redArg(v_m_3210_, v_query_3211_, v_x_3212_, v_x_3213_, v_x_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4___boxed(lean_object* v_00_u03b2_3217_, lean_object* v_m_3218_, lean_object* v_query_3219_, lean_object* v_x_3220_, lean_object* v_x_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__4(v_00_u03b2_3217_, v_m_3218_, v_query_3219_, v_x_3220_, v_x_3221_, v_x_3222_, v_x_3223_);
lean_dec(v_query_3219_);
lean_dec_ref(v_m_3218_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6(lean_object* v_00_u03b2_3225_, lean_object* v_init_3226_, lean_object* v_b_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6___redArg(v_init_3226_, v_b_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3229_, lean_object* v_init_3230_, lean_object* v_b_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6(v_00_u03b2_3229_, v_init_3230_, v_b_3231_);
lean_dec_ref(v_b_3231_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4(lean_object* v_e_3233_, lean_object* v_a_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4___redArg(v_e_3233_, v_a_3234_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4___boxed(lean_object* v_e_3242_, lean_object* v_a_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4(v_e_3242_, v_a_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec(v_a_3243_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_3251_, lean_object* v_b_3252_, lean_object* v_acc_3253_, lean_object* v_i_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9___redArg(v_b_3252_, v_acc_3253_, v_i_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3256_, lean_object* v_b_3257_, lean_object* v_acc_3258_, lean_object* v_i_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__6_spec__9(v_00_u03b2_3256_, v_b_3257_, v_acc_3258_, v_i_3259_);
lean_dec_ref(v_b_3257_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22(lean_object* v_a_3261_, lean_object* v_as_3262_, size_t v_sz_3263_, size_t v_i_3264_, lean_object* v_b_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22___redArg(v_a_3261_, v_as_3262_, v_sz_3263_, v_i_3264_, v_b_3265_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22___boxed(lean_object* v_a_3272_, lean_object* v_as_3273_, lean_object* v_sz_3274_, lean_object* v_i_3275_, lean_object* v_b_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
size_t v_sz_boxed_3282_; size_t v_i_boxed_3283_; lean_object* v_res_3284_; 
v_sz_boxed_3282_ = lean_unbox_usize(v_sz_3274_);
lean_dec(v_sz_3274_);
v_i_boxed_3283_ = lean_unbox_usize(v_i_3275_);
lean_dec(v_i_3275_);
v_res_3284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__13_spec__22(v_a_3272_, v_as_3273_, v_sz_boxed_3282_, v_i_boxed_3283_, v_b_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec_ref(v_as_3273_);
lean_dec_ref(v_a_3272_);
return v_res_3284_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10(lean_object* v_00_u03b2_3285_, lean_object* v_m_3286_, lean_object* v_a_3287_){
_start:
{
uint8_t v___x_3288_; 
v___x_3288_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10___redArg(v_m_3286_, v_a_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10___boxed(lean_object* v_00_u03b2_3289_, lean_object* v_m_3290_, lean_object* v_a_3291_){
_start:
{
uint8_t v_res_3292_; lean_object* v_r_3293_; 
v_res_3292_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10(v_00_u03b2_3289_, v_m_3290_, v_a_3291_);
lean_dec_ref(v_a_3291_);
lean_dec_ref(v_m_3290_);
v_r_3293_ = lean_box(v_res_3292_);
return v_r_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11(lean_object* v_00_u03b2_3294_, lean_object* v_m_3295_, lean_object* v_query_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___redArg(v_m_3295_, v_query_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11___boxed(lean_object* v_00_u03b2_3298_, lean_object* v_m_3299_, lean_object* v_query_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11(v_00_u03b2_3298_, v_m_3299_, v_query_3300_);
lean_dec_ref(v_query_3300_);
lean_dec_ref(v_m_3299_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_3302_, lean_object* v_m_3303_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___redArg(v_m_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12___boxed(lean_object* v_00_u03b2_3305_, lean_object* v_m_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12(v_00_u03b2_3305_, v_m_3306_);
lean_dec_ref(v_m_3306_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25(lean_object* v_a_3308_, lean_object* v_as_3309_, size_t v_sz_3310_, size_t v_i_3311_, lean_object* v_b_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25___redArg(v_a_3308_, v_as_3309_, v_sz_3310_, v_i_3311_, v_b_3312_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25___boxed(lean_object* v_a_3319_, lean_object* v_as_3320_, lean_object* v_sz_3321_, lean_object* v_i_3322_, lean_object* v_b_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
size_t v_sz_boxed_3329_; size_t v_i_boxed_3330_; lean_object* v_res_3331_; 
v_sz_boxed_3329_ = lean_unbox_usize(v_sz_3321_);
lean_dec(v_sz_3321_);
v_i_boxed_3330_ = lean_unbox_usize(v_i_3322_);
lean_dec(v_i_3322_);
v_res_3331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__6_spec__12_spec__20_spec__25(v_a_3319_, v_as_3320_, v_sz_boxed_3329_, v_i_boxed_3330_, v_b_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec_ref(v_as_3320_);
lean_dec_ref(v_a_3319_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17(lean_object* v_00_u03b2_3332_, lean_object* v_m_3333_, lean_object* v_query_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17___redArg(v_m_3333_, v_query_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3336_, lean_object* v_m_3337_, lean_object* v_query_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__10_spec__17(v_00_u03b2_3336_, v_m_3337_, v_query_3338_);
lean_dec_ref(v_query_3338_);
lean_dec_ref(v_m_3337_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19(lean_object* v_00_u03b2_3340_, lean_object* v_m_3341_, lean_object* v_query_3342_, lean_object* v_x_3343_, lean_object* v_x_3344_, lean_object* v_x_3345_, lean_object* v_x_3346_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19___redArg(v_m_3341_, v_query_3342_, v_x_3343_, v_x_3344_, v_x_3345_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19___boxed(lean_object* v_00_u03b2_3348_, lean_object* v_m_3349_, lean_object* v_query_3350_, lean_object* v_x_3351_, lean_object* v_x_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__11_spec__19(v_00_u03b2_3348_, v_m_3349_, v_query_3350_, v_x_3351_, v_x_3352_, v_x_3353_, v_x_3354_);
lean_dec_ref(v_query_3350_);
lean_dec_ref(v_m_3349_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21(lean_object* v_00_u03b2_3356_, lean_object* v_init_3357_, lean_object* v_b_3358_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21___redArg(v_init_3357_, v_b_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21___boxed(lean_object* v_00_u03b2_3360_, lean_object* v_init_3361_, lean_object* v_b_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21(v_00_u03b2_3360_, v_init_3361_, v_b_3362_);
lean_dec_ref(v_b_3362_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29(lean_object* v_00_u03b2_3364_, lean_object* v_b_3365_, lean_object* v_acc_3366_, lean_object* v_i_3367_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29___redArg(v_b_3365_, v_acc_3366_, v_i_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29___boxed(lean_object* v_00_u03b2_3369_, lean_object* v_b_3370_, lean_object* v_acc_3371_, lean_object* v_i_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__2_spec__4_spec__12_spec__21_spec__29(v_00_u03b2_3369_, v_b_3370_, v_acc_3371_, v_i_3372_);
lean_dec_ref(v_b_3370_);
return v_res_3373_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = l_Lean_maxRecDepthErrorMessage;
v___x_3380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
return v___x_3380_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_3382_ = l_Lean_MessageData_ofFormat(v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_3384_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_3385_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
lean_ctor_set(v___x_3385_, 1, v___x_3383_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_3386_){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3389_, 0, v_ref_3386_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3391_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_3394_, lean_object* v_ref_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3395_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_3403_, lean_object* v_ref_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_3403_, v_ref_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_3412_, lean_object* v_mvarId_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_fileName_3420_; lean_object* v_fileMap_3421_; lean_object* v_options_3422_; lean_object* v_currRecDepth_3423_; lean_object* v_maxRecDepth_3424_; lean_object* v_ref_3425_; lean_object* v_currNamespace_3426_; lean_object* v_openDecls_3427_; lean_object* v_initHeartbeats_3428_; lean_object* v_maxHeartbeats_3429_; lean_object* v_quotContext_3430_; lean_object* v_currMacroScope_3431_; uint8_t v_diag_3432_; lean_object* v_cancelTk_x3f_3433_; uint8_t v_suppressElabErrors_3434_; lean_object* v_inheritedTraceOptions_3435_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v_fileName_3420_ = lean_ctor_get(v_a_3417_, 0);
v_fileMap_3421_ = lean_ctor_get(v_a_3417_, 1);
v_options_3422_ = lean_ctor_get(v_a_3417_, 2);
v_currRecDepth_3423_ = lean_ctor_get(v_a_3417_, 3);
v_maxRecDepth_3424_ = lean_ctor_get(v_a_3417_, 4);
v_ref_3425_ = lean_ctor_get(v_a_3417_, 5);
v_currNamespace_3426_ = lean_ctor_get(v_a_3417_, 6);
v_openDecls_3427_ = lean_ctor_get(v_a_3417_, 7);
v_initHeartbeats_3428_ = lean_ctor_get(v_a_3417_, 8);
v_maxHeartbeats_3429_ = lean_ctor_get(v_a_3417_, 9);
v_quotContext_3430_ = lean_ctor_get(v_a_3417_, 10);
v_currMacroScope_3431_ = lean_ctor_get(v_a_3417_, 11);
v_diag_3432_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*14);
v_cancelTk_x3f_3433_ = lean_ctor_get(v_a_3417_, 12);
v_suppressElabErrors_3434_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3435_ = lean_ctor_get(v_a_3417_, 13);
v___x_3463_ = lean_unsigned_to_nat(0u);
v___x_3464_ = lean_nat_dec_eq(v_maxRecDepth_3424_, v___x_3463_);
if (v___x_3464_ == 0)
{
uint8_t v___x_3465_; 
v___x_3465_ = lean_nat_dec_eq(v_currRecDepth_3423_, v_maxRecDepth_3424_);
if (v___x_3465_ == 0)
{
goto v___jp_3436_;
}
else
{
lean_object* v___x_3466_; 
lean_dec(v_mvarId_3413_);
lean_dec_ref(v_x_3412_);
lean_inc(v_ref_3425_);
v___x_3466_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3425_);
return v___x_3466_;
}
}
else
{
goto v___jp_3436_;
}
v___jp_3436_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3437_ = lean_unsigned_to_nat(1u);
v___x_3438_ = lean_nat_add(v_currRecDepth_3423_, v___x_3437_);
lean_inc_ref(v_inheritedTraceOptions_3435_);
lean_inc(v_cancelTk_x3f_3433_);
lean_inc(v_currMacroScope_3431_);
lean_inc(v_quotContext_3430_);
lean_inc(v_maxHeartbeats_3429_);
lean_inc(v_initHeartbeats_3428_);
lean_inc(v_openDecls_3427_);
lean_inc(v_currNamespace_3426_);
lean_inc(v_ref_3425_);
lean_inc(v_maxRecDepth_3424_);
lean_inc_ref(v_options_3422_);
lean_inc_ref(v_fileMap_3421_);
lean_inc_ref(v_fileName_3420_);
v___x_3439_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3439_, 0, v_fileName_3420_);
lean_ctor_set(v___x_3439_, 1, v_fileMap_3421_);
lean_ctor_set(v___x_3439_, 2, v_options_3422_);
lean_ctor_set(v___x_3439_, 3, v___x_3438_);
lean_ctor_set(v___x_3439_, 4, v_maxRecDepth_3424_);
lean_ctor_set(v___x_3439_, 5, v_ref_3425_);
lean_ctor_set(v___x_3439_, 6, v_currNamespace_3426_);
lean_ctor_set(v___x_3439_, 7, v_openDecls_3427_);
lean_ctor_set(v___x_3439_, 8, v_initHeartbeats_3428_);
lean_ctor_set(v___x_3439_, 9, v_maxHeartbeats_3429_);
lean_ctor_set(v___x_3439_, 10, v_quotContext_3430_);
lean_ctor_set(v___x_3439_, 11, v_currMacroScope_3431_);
lean_ctor_set(v___x_3439_, 12, v_cancelTk_x3f_3433_);
lean_ctor_set(v___x_3439_, 13, v_inheritedTraceOptions_3435_);
lean_ctor_set_uint8(v___x_3439_, sizeof(void*)*14, v_diag_3432_);
lean_ctor_set_uint8(v___x_3439_, sizeof(void*)*14 + 1, v_suppressElabErrors_3434_);
lean_inc_ref(v_x_3412_);
lean_inc(v_a_3418_);
lean_inc_ref(v___x_3439_);
lean_inc(v_a_3416_);
lean_inc_ref(v_a_3415_);
lean_inc(v_mvarId_3413_);
v___x_3440_ = lean_apply_6(v_x_3412_, v_mvarId_3413_, v_a_3415_, v_a_3416_, v___x_3439_, v_a_3418_, lean_box(0));
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3454_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3454_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3454_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
if (lean_obj_tag(v_a_3441_) == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
lean_dec_ref_known(v___x_3439_, 14);
lean_dec_ref(v_x_3412_);
v___x_3445_ = lean_st_ref_take(v_a_3414_);
v___x_3446_ = lean_array_push(v___x_3445_, v_mvarId_3413_);
v___x_3447_ = lean_st_ref_put(v_a_3414_, v___x_3446_);
v___x_3448_ = lean_box(0);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3448_);
v___x_3450_ = v___x_3443_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
else
{
lean_object* v_val_3452_; lean_object* v___x_3453_; 
lean_del_object(v___x_3443_);
lean_dec(v_mvarId_3413_);
v_val_3452_ = lean_ctor_get(v_a_3441_, 0);
lean_inc(v_val_3452_);
lean_dec_ref_known(v_a_3441_, 1);
v___x_3453_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3412_, v_val_3452_, v_a_3414_, v_a_3415_, v_a_3416_, v___x_3439_, v_a_3418_);
lean_dec_ref_known(v___x_3439_, 14);
return v___x_3453_;
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec_ref_known(v___x_3439_, 14);
lean_dec(v_mvarId_3413_);
lean_dec_ref(v_x_3412_);
v_a_3455_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3440_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3440_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3467_, lean_object* v_as_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
if (lean_obj_tag(v_as_3468_) == 0)
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
lean_dec_ref(v_x_3467_);
v___x_3475_ = lean_box(0);
v___x_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
return v___x_3476_;
}
else
{
lean_object* v_head_3477_; lean_object* v_tail_3478_; lean_object* v___x_3479_; 
v_head_3477_ = lean_ctor_get(v_as_3468_, 0);
lean_inc(v_head_3477_);
v_tail_3478_ = lean_ctor_get(v_as_3468_, 1);
lean_inc(v_tail_3478_);
lean_dec_ref_known(v_as_3468_, 2);
lean_inc_ref(v_x_3467_);
v___x_3479_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3467_, v_head_3477_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_dec_ref_known(v___x_3479_, 1);
v_as_3468_ = v_tail_3478_;
goto _start;
}
else
{
lean_dec(v_tail_3478_);
lean_dec_ref(v_x_3467_);
return v___x_3479_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3481_, lean_object* v_as_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3481_, v_as_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3490_, lean_object* v_mvarId_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3490_, v_mvarId_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_);
lean_dec(v_a_3496_);
lean_dec_ref(v_a_3495_);
lean_dec(v_a_3494_);
lean_dec_ref(v_a_3493_);
lean_dec(v_a_3492_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3499_, lean_object* v_x_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3507_ = lean_st_mk_ref(v___x_3506_);
v___x_3508_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3500_, v_mvarId_3499_, v___x_3507_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3517_; 
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3517_ == 0)
{
lean_object* v_unused_3518_; 
v_unused_3518_ = lean_ctor_get(v___x_3508_, 0);
lean_dec(v_unused_3518_);
v___x_3510_ = v___x_3508_;
v_isShared_3511_ = v_isSharedCheck_3517_;
goto v_resetjp_3509_;
}
else
{
lean_dec(v___x_3508_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3517_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3512_ = lean_st_ref_get(v___x_3507_);
lean_dec(v___x_3507_);
v___x_3513_ = lean_array_to_list(v___x_3512_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3513_);
v___x_3515_ = v___x_3510_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec(v___x_3507_);
v_a_3519_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3508_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3508_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3527_, lean_object* v_x_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_Meta_saturate(v_mvarId_3527_, v_x_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3535_, lean_object* v_msg_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
if (lean_obj_tag(v_mvarIds_3535_) == 1)
{
lean_object* v_tail_3542_; 
v_tail_3542_ = lean_ctor_get(v_mvarIds_3535_, 1);
if (lean_obj_tag(v_tail_3542_) == 0)
{
lean_object* v_head_3543_; lean_object* v___x_3544_; 
lean_dec_ref(v_msg_3536_);
v_head_3543_ = lean_ctor_get(v_mvarIds_3535_, 0);
lean_inc(v_head_3543_);
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v_head_3543_);
return v___x_3544_;
}
else
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
return v___x_3545_;
}
}
else
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
return v___x_3546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3547_, lean_object* v_msg_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_Meta_exactlyOne(v_mvarIds_3547_, v_msg_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_mvarIds_3547_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3555_, lean_object* v_msg_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
if (lean_obj_tag(v_mvarIds_3555_) == 0)
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec_ref(v_msg_3556_);
v___x_3562_ = lean_box(0);
v___x_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
return v___x_3563_;
}
else
{
lean_object* v_tail_3564_; 
v_tail_3564_ = lean_ctor_get(v_mvarIds_3555_, 1);
if (lean_obj_tag(v_tail_3564_) == 0)
{
lean_object* v_head_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
lean_dec_ref(v_msg_3556_);
v_head_3565_ = lean_ctor_get(v_mvarIds_3555_, 0);
lean_inc(v_head_3565_);
v___x_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3566_, 0, v_head_3565_);
v___x_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
return v___x_3567_;
}
else
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
return v___x_3568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3569_, lean_object* v_msg_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3569_, v_msg_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_mvarIds_3569_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3577_, size_t v_sz_3578_, size_t v_i_3579_, lean_object* v_b_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_usize_dec_lt(v_i_3579_, v_sz_3578_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; 
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v_b_3580_);
return v___x_3587_;
}
else
{
lean_object* v_snd_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3618_; 
v_snd_3588_ = lean_ctor_get(v_b_3580_, 1);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_b_3580_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; 
v_unused_3619_ = lean_ctor_get(v_b_3580_, 0);
lean_dec(v_unused_3619_);
v___x_3590_ = v_b_3580_;
v_isShared_3591_ = v_isSharedCheck_3618_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_snd_3588_);
lean_dec(v_b_3580_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3618_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3592_; lean_object* v_a_3594_; lean_object* v_a_3601_; 
v___x_3592_ = lean_box(0);
v_a_3601_ = lean_array_uget_borrowed(v_as_3577_, v_i_3579_);
if (lean_obj_tag(v_a_3601_) == 0)
{
v_a_3594_ = v_snd_3588_;
goto v___jp_3593_;
}
else
{
lean_object* v_val_3602_; uint8_t v___x_3603_; 
v_val_3602_ = lean_ctor_get(v_a_3601_, 0);
v___x_3603_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3602_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = l_Lean_LocalDecl_type(v_val_3602_);
v___x_3605_ = l_Lean_Meta_isProp(v___x_3604_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; uint8_t v___x_3607_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___x_3605_, 1);
v___x_3607_ = lean_unbox(v_a_3606_);
lean_dec(v_a_3606_);
if (v___x_3607_ == 0)
{
v_a_3594_ = v_snd_3588_;
goto v___jp_3593_;
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = l_Lean_LocalDecl_fvarId(v_val_3602_);
v___x_3609_ = lean_array_push(v_snd_3588_, v___x_3608_);
v_a_3594_ = v___x_3609_;
goto v___jp_3593_;
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_del_object(v___x_3590_);
lean_dec(v_snd_3588_);
v_a_3610_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3605_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3605_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
v_a_3594_ = v_snd_3588_;
goto v___jp_3593_;
}
}
v___jp_3593_:
{
lean_object* v___x_3596_; 
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 1, v_a_3594_);
lean_ctor_set(v___x_3590_, 0, v___x_3592_);
v___x_3596_ = v___x_3590_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_a_3594_);
v___x_3596_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
size_t v___x_3597_; size_t v___x_3598_; 
v___x_3597_ = ((size_t)1ULL);
v___x_3598_ = lean_usize_add(v_i_3579_, v___x_3597_);
v_i_3579_ = v___x_3598_;
v_b_3580_ = v___x_3596_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3620_, lean_object* v_sz_3621_, lean_object* v_i_3622_, lean_object* v_b_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
size_t v_sz_boxed_3629_; size_t v_i_boxed_3630_; lean_object* v_res_3631_; 
v_sz_boxed_3629_ = lean_unbox_usize(v_sz_3621_);
lean_dec(v_sz_3621_);
v_i_boxed_3630_ = lean_unbox_usize(v_i_3622_);
lean_dec(v_i_3622_);
v_res_3631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3620_, v_sz_boxed_3629_, v_i_boxed_3630_, v_b_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec_ref(v_as_3620_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3632_, size_t v_sz_3633_, size_t v_i_3634_, lean_object* v_b_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
uint8_t v___x_3641_; 
v___x_3641_ = lean_usize_dec_lt(v_i_3634_, v_sz_3633_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; 
v___x_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3642_, 0, v_b_3635_);
return v___x_3642_;
}
else
{
lean_object* v_snd_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3673_; 
v_snd_3643_ = lean_ctor_get(v_b_3635_, 1);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_b_3635_);
if (v_isSharedCheck_3673_ == 0)
{
lean_object* v_unused_3674_; 
v_unused_3674_ = lean_ctor_get(v_b_3635_, 0);
lean_dec(v_unused_3674_);
v___x_3645_ = v_b_3635_;
v_isShared_3646_ = v_isSharedCheck_3673_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_snd_3643_);
lean_dec(v_b_3635_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3673_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v_a_3649_; lean_object* v_a_3656_; 
v___x_3647_ = lean_box(0);
v_a_3656_ = lean_array_uget_borrowed(v_as_3632_, v_i_3634_);
if (lean_obj_tag(v_a_3656_) == 0)
{
v_a_3649_ = v_snd_3643_;
goto v___jp_3648_;
}
else
{
lean_object* v_val_3657_; uint8_t v___x_3658_; 
v_val_3657_ = lean_ctor_get(v_a_3656_, 0);
v___x_3658_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3657_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = l_Lean_LocalDecl_type(v_val_3657_);
v___x_3660_ = l_Lean_Meta_isProp(v___x_3659_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; uint8_t v___x_3662_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3660_, 1);
v___x_3662_ = lean_unbox(v_a_3661_);
lean_dec(v_a_3661_);
if (v___x_3662_ == 0)
{
v_a_3649_ = v_snd_3643_;
goto v___jp_3648_;
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = l_Lean_LocalDecl_fvarId(v_val_3657_);
v___x_3664_ = lean_array_push(v_snd_3643_, v___x_3663_);
v_a_3649_ = v___x_3664_;
goto v___jp_3648_;
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_del_object(v___x_3645_);
lean_dec(v_snd_3643_);
v_a_3665_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3660_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3660_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
else
{
v_a_3649_ = v_snd_3643_;
goto v___jp_3648_;
}
}
v___jp_3648_:
{
lean_object* v___x_3651_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 1, v_a_3649_);
lean_ctor_set(v___x_3645_, 0, v___x_3647_);
v___x_3651_ = v___x_3645_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_a_3649_);
v___x_3651_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
size_t v___x_3652_; size_t v___x_3653_; lean_object* v___x_3654_; 
v___x_3652_ = ((size_t)1ULL);
v___x_3653_ = lean_usize_add(v_i_3634_, v___x_3652_);
v___x_3654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3632_, v_sz_3633_, v___x_3653_, v___x_3651_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
return v___x_3654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3675_, lean_object* v_sz_3676_, lean_object* v_i_3677_, lean_object* v_b_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
size_t v_sz_boxed_3684_; size_t v_i_boxed_3685_; lean_object* v_res_3686_; 
v_sz_boxed_3684_ = lean_unbox_usize(v_sz_3676_);
lean_dec(v_sz_3676_);
v_i_boxed_3685_ = lean_unbox_usize(v_i_3677_);
lean_dec(v_i_3677_);
v_res_3686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3675_, v_sz_boxed_3684_, v_i_boxed_3685_, v_b_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec_ref(v_as_3675_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_init_3687_, lean_object* v_n_3688_, lean_object* v_b_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
if (lean_obj_tag(v_n_3688_) == 0)
{
lean_object* v_cs_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; size_t v_sz_3698_; size_t v___x_3699_; lean_object* v___x_3700_; 
v_cs_3695_ = lean_ctor_get(v_n_3688_, 0);
v___x_3696_ = lean_box(0);
v___x_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
lean_ctor_set(v___x_3697_, 1, v_b_3689_);
v_sz_3698_ = lean_array_size(v_cs_3695_);
v___x_3699_ = ((size_t)0ULL);
v___x_3700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3687_, v_cs_3695_, v_sz_3698_, v___x_3699_, v___x_3697_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3715_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3715_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3715_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v_fst_3705_; 
v_fst_3705_ = lean_ctor_get(v_a_3701_, 0);
if (lean_obj_tag(v_fst_3705_) == 0)
{
lean_object* v_snd_3706_; lean_object* v___x_3707_; lean_object* v___x_3709_; 
v_snd_3706_ = lean_ctor_get(v_a_3701_, 1);
lean_inc(v_snd_3706_);
lean_dec(v_a_3701_);
v___x_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3707_, 0, v_snd_3706_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3707_);
v___x_3709_ = v___x_3703_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
else
{
lean_object* v_val_3711_; lean_object* v___x_3713_; 
lean_inc_ref(v_fst_3705_);
lean_dec(v_a_3701_);
v_val_3711_ = lean_ctor_get(v_fst_3705_, 0);
lean_inc(v_val_3711_);
lean_dec_ref_known(v_fst_3705_, 1);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v_val_3711_);
v___x_3713_ = v___x_3703_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_val_3711_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
v_a_3716_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3700_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3700_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v_vs_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; size_t v_sz_3727_; size_t v___x_3728_; lean_object* v___x_3729_; 
v_vs_3724_ = lean_ctor_get(v_n_3688_, 0);
v___x_3725_ = lean_box(0);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
lean_ctor_set(v___x_3726_, 1, v_b_3689_);
v_sz_3727_ = lean_array_size(v_vs_3724_);
v___x_3728_ = ((size_t)0ULL);
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3724_, v_sz_3727_, v___x_3728_, v___x_3726_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3744_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3732_ = v___x_3729_;
v_isShared_3733_ = v_isSharedCheck_3744_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3729_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3744_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v_fst_3734_; 
v_fst_3734_ = lean_ctor_get(v_a_3730_, 0);
if (lean_obj_tag(v_fst_3734_) == 0)
{
lean_object* v_snd_3735_; lean_object* v___x_3736_; lean_object* v___x_3738_; 
v_snd_3735_ = lean_ctor_get(v_a_3730_, 1);
lean_inc(v_snd_3735_);
lean_dec(v_a_3730_);
v___x_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3736_, 0, v_snd_3735_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 0, v___x_3736_);
v___x_3738_ = v___x_3732_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
else
{
lean_object* v_val_3740_; lean_object* v___x_3742_; 
lean_inc_ref(v_fst_3734_);
lean_dec(v_a_3730_);
v_val_3740_ = lean_ctor_get(v_fst_3734_, 0);
lean_inc(v_val_3740_);
lean_dec_ref_known(v_fst_3734_, 1);
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 0, v_val_3740_);
v___x_3742_ = v___x_3732_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_val_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
v_a_3745_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3729_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3729_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_init_3753_, lean_object* v_as_3754_, size_t v_sz_3755_, size_t v_i_3756_, lean_object* v_b_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
uint8_t v___x_3763_; 
v___x_3763_ = lean_usize_dec_lt(v_i_3756_, v_sz_3755_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; 
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_b_3757_);
return v___x_3764_;
}
else
{
lean_object* v_snd_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3799_; 
v_snd_3765_ = lean_ctor_get(v_b_3757_, 1);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_b_3757_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; 
v_unused_3800_ = lean_ctor_get(v_b_3757_, 0);
lean_dec(v_unused_3800_);
v___x_3767_ = v_b_3757_;
v_isShared_3768_ = v_isSharedCheck_3799_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_snd_3765_);
lean_dec(v_b_3757_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3799_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v_a_3769_; lean_object* v___x_3770_; 
v_a_3769_ = lean_array_uget_borrowed(v_as_3754_, v_i_3756_);
lean_inc(v_snd_3765_);
v___x_3770_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3753_, v_a_3769_, v_snd_3765_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3790_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3773_ = v___x_3770_;
v_isShared_3774_ = v_isSharedCheck_3790_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3790_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
if (lean_obj_tag(v_a_3771_) == 0)
{
lean_object* v___x_3775_; lean_object* v___x_3777_; 
v___x_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3775_, 0, v_a_3771_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v___x_3775_);
v___x_3777_ = v___x_3767_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_snd_3765_);
v___x_3777_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3779_; 
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 0, v___x_3777_);
v___x_3779_ = v___x_3773_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3783_; lean_object* v___x_3785_; 
lean_del_object(v___x_3773_);
lean_dec(v_snd_3765_);
v_a_3782_ = lean_ctor_get(v_a_3771_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v_a_3771_, 1);
v___x_3783_ = lean_box(0);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v_a_3782_);
lean_ctor_set(v___x_3767_, 0, v___x_3783_);
v___x_3785_ = v___x_3767_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_a_3782_);
v___x_3785_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
size_t v___x_3786_; size_t v___x_3787_; 
v___x_3786_ = ((size_t)1ULL);
v___x_3787_ = lean_usize_add(v_i_3756_, v___x_3786_);
v_i_3756_ = v___x_3787_;
v_b_3757_ = v___x_3785_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_del_object(v___x_3767_);
lean_dec(v_snd_3765_);
v_a_3791_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3770_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3770_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3801_, lean_object* v_as_3802_, lean_object* v_sz_3803_, lean_object* v_i_3804_, lean_object* v_b_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
size_t v_sz_boxed_3811_; size_t v_i_boxed_3812_; lean_object* v_res_3813_; 
v_sz_boxed_3811_ = lean_unbox_usize(v_sz_3803_);
lean_dec(v_sz_3803_);
v_i_boxed_3812_ = lean_unbox_usize(v_i_3804_);
lean_dec(v_i_3804_);
v_res_3813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3801_, v_as_3802_, v_sz_boxed_3811_, v_i_boxed_3812_, v_b_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec_ref(v_as_3802_);
lean_dec_ref(v_init_3801_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_init_3814_, lean_object* v_n_3815_, lean_object* v_b_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3814_, v_n_3815_, v_b_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec_ref(v_n_3815_);
lean_dec_ref(v_init_3814_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3823_, size_t v_sz_3824_, size_t v_i_3825_, lean_object* v_b_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
uint8_t v___x_3832_; 
v___x_3832_ = lean_usize_dec_lt(v_i_3825_, v_sz_3824_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; 
v___x_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3833_, 0, v_b_3826_);
return v___x_3833_;
}
else
{
lean_object* v_snd_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3864_; 
v_snd_3834_ = lean_ctor_get(v_b_3826_, 1);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_b_3826_);
if (v_isSharedCheck_3864_ == 0)
{
lean_object* v_unused_3865_; 
v_unused_3865_ = lean_ctor_get(v_b_3826_, 0);
lean_dec(v_unused_3865_);
v___x_3836_ = v_b_3826_;
v_isShared_3837_ = v_isSharedCheck_3864_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_snd_3834_);
lean_dec(v_b_3826_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3864_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3838_; lean_object* v_a_3840_; lean_object* v_a_3847_; 
v___x_3838_ = lean_box(0);
v_a_3847_ = lean_array_uget_borrowed(v_as_3823_, v_i_3825_);
if (lean_obj_tag(v_a_3847_) == 0)
{
v_a_3840_ = v_snd_3834_;
goto v___jp_3839_;
}
else
{
lean_object* v_val_3848_; uint8_t v___x_3849_; 
v_val_3848_ = lean_ctor_get(v_a_3847_, 0);
v___x_3849_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3848_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = l_Lean_LocalDecl_type(v_val_3848_);
v___x_3851_ = l_Lean_Meta_isProp(v___x_3850_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; uint8_t v___x_3853_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3853_ = lean_unbox(v_a_3852_);
lean_dec(v_a_3852_);
if (v___x_3853_ == 0)
{
v_a_3840_ = v_snd_3834_;
goto v___jp_3839_;
}
else
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = l_Lean_LocalDecl_fvarId(v_val_3848_);
v___x_3855_ = lean_array_push(v_snd_3834_, v___x_3854_);
v_a_3840_ = v___x_3855_;
goto v___jp_3839_;
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_del_object(v___x_3836_);
lean_dec(v_snd_3834_);
v_a_3856_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3851_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3851_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
else
{
v_a_3840_ = v_snd_3834_;
goto v___jp_3839_;
}
}
v___jp_3839_:
{
lean_object* v___x_3842_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 1, v_a_3840_);
lean_ctor_set(v___x_3836_, 0, v___x_3838_);
v___x_3842_ = v___x_3836_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v_a_3840_);
v___x_3842_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
size_t v___x_3843_; size_t v___x_3844_; 
v___x_3843_ = ((size_t)1ULL);
v___x_3844_ = lean_usize_add(v_i_3825_, v___x_3843_);
v_i_3825_ = v___x_3844_;
v_b_3826_ = v___x_3842_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3866_, lean_object* v_sz_3867_, lean_object* v_i_3868_, lean_object* v_b_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
size_t v_sz_boxed_3875_; size_t v_i_boxed_3876_; lean_object* v_res_3877_; 
v_sz_boxed_3875_ = lean_unbox_usize(v_sz_3867_);
lean_dec(v_sz_3867_);
v_i_boxed_3876_ = lean_unbox_usize(v_i_3868_);
lean_dec(v_i_3868_);
v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3866_, v_sz_boxed_3875_, v_i_boxed_3876_, v_b_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec_ref(v_as_3866_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3878_, size_t v_sz_3879_, size_t v_i_3880_, lean_object* v_b_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
uint8_t v___x_3887_; 
v___x_3887_ = lean_usize_dec_lt(v_i_3880_, v_sz_3879_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; 
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v_b_3881_);
return v___x_3888_;
}
else
{
lean_object* v_snd_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3919_; 
v_snd_3889_ = lean_ctor_get(v_b_3881_, 1);
v_isSharedCheck_3919_ = !lean_is_exclusive(v_b_3881_);
if (v_isSharedCheck_3919_ == 0)
{
lean_object* v_unused_3920_; 
v_unused_3920_ = lean_ctor_get(v_b_3881_, 0);
lean_dec(v_unused_3920_);
v___x_3891_ = v_b_3881_;
v_isShared_3892_ = v_isSharedCheck_3919_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_snd_3889_);
lean_dec(v_b_3881_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3919_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v_a_3895_; lean_object* v_a_3902_; 
v___x_3893_ = lean_box(0);
v_a_3902_ = lean_array_uget_borrowed(v_as_3878_, v_i_3880_);
if (lean_obj_tag(v_a_3902_) == 0)
{
v_a_3895_ = v_snd_3889_;
goto v___jp_3894_;
}
else
{
lean_object* v_val_3903_; uint8_t v___x_3904_; 
v_val_3903_ = lean_ctor_get(v_a_3902_, 0);
v___x_3904_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3903_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = l_Lean_LocalDecl_type(v_val_3903_);
v___x_3906_ = l_Lean_Meta_isProp(v___x_3905_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; uint8_t v___x_3908_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3906_, 1);
v___x_3908_ = lean_unbox(v_a_3907_);
lean_dec(v_a_3907_);
if (v___x_3908_ == 0)
{
v_a_3895_ = v_snd_3889_;
goto v___jp_3894_;
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = l_Lean_LocalDecl_fvarId(v_val_3903_);
v___x_3910_ = lean_array_push(v_snd_3889_, v___x_3909_);
v_a_3895_ = v___x_3910_;
goto v___jp_3894_;
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
lean_del_object(v___x_3891_);
lean_dec(v_snd_3889_);
v_a_3911_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3906_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3906_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
else
{
v_a_3895_ = v_snd_3889_;
goto v___jp_3894_;
}
}
v___jp_3894_:
{
lean_object* v___x_3897_; 
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 1, v_a_3895_);
lean_ctor_set(v___x_3891_, 0, v___x_3893_);
v___x_3897_ = v___x_3891_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_a_3895_);
v___x_3897_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
size_t v___x_3898_; size_t v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = ((size_t)1ULL);
v___x_3899_ = lean_usize_add(v_i_3880_, v___x_3898_);
v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3878_, v_sz_3879_, v___x_3899_, v___x_3897_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3921_, lean_object* v_sz_3922_, lean_object* v_i_3923_, lean_object* v_b_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
size_t v_sz_boxed_3930_; size_t v_i_boxed_3931_; lean_object* v_res_3932_; 
v_sz_boxed_3930_ = lean_unbox_usize(v_sz_3922_);
lean_dec(v_sz_3922_);
v_i_boxed_3931_ = lean_unbox_usize(v_i_3923_);
lean_dec(v_i_3923_);
v_res_3932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3921_, v_sz_boxed_3930_, v_i_boxed_3931_, v_b_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec_ref(v_as_3921_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3933_, lean_object* v_init_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_root_3940_; lean_object* v_tail_3941_; lean_object* v___x_3942_; 
v_root_3940_ = lean_ctor_get(v_t_3933_, 0);
v_tail_3941_ = lean_ctor_get(v_t_3933_, 1);
lean_inc_ref(v_init_3934_);
v___x_3942_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3934_, v_root_3940_, v_init_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec_ref(v_init_3934_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3979_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3979_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3979_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
if (lean_obj_tag(v_a_3943_) == 0)
{
lean_object* v_a_3947_; lean_object* v___x_3949_; 
v_a_3947_ = lean_ctor_get(v_a_3943_, 0);
lean_inc(v_a_3947_);
lean_dec_ref_known(v_a_3943_, 1);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v_a_3947_);
v___x_3949_ = v___x_3945_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3947_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; size_t v_sz_3954_; size_t v___x_3955_; lean_object* v___x_3956_; 
lean_del_object(v___x_3945_);
v_a_3951_ = lean_ctor_get(v_a_3943_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v_a_3943_, 1);
v___x_3952_ = lean_box(0);
v___x_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
lean_ctor_set(v___x_3953_, 1, v_a_3951_);
v_sz_3954_ = lean_array_size(v_tail_3941_);
v___x_3955_ = ((size_t)0ULL);
v___x_3956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3941_, v_sz_3954_, v___x_3955_, v___x_3953_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3970_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3970_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3970_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v_fst_3961_; 
v_fst_3961_ = lean_ctor_get(v_a_3957_, 0);
if (lean_obj_tag(v_fst_3961_) == 0)
{
lean_object* v_snd_3962_; lean_object* v___x_3964_; 
v_snd_3962_ = lean_ctor_get(v_a_3957_, 1);
lean_inc(v_snd_3962_);
lean_dec(v_a_3957_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v_snd_3962_);
v___x_3964_ = v___x_3959_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_snd_3962_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
else
{
lean_object* v_val_3966_; lean_object* v___x_3968_; 
lean_inc_ref(v_fst_3961_);
lean_dec(v_a_3957_);
v_val_3966_ = lean_ctor_get(v_fst_3961_, 0);
lean_inc(v_val_3966_);
lean_dec_ref_known(v_fst_3961_, 1);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v_val_3966_);
v___x_3968_ = v___x_3959_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_val_3966_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
v_a_3971_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3956_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3956_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
v_a_3980_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3942_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3942_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3988_, lean_object* v_init_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3988_, v_init_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec_ref(v_t_3988_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_lctx_4001_; lean_object* v_decls_4002_; lean_object* v_result_4003_; lean_object* v___x_4004_; 
v_lctx_4001_ = lean_ctor_get(v_a_3996_, 2);
v_decls_4002_ = lean_ctor_get(v_lctx_4001_, 1);
v_result_4003_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_4004_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_4002_, v_result_4003_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l_Lean_Meta_getPropHyps(v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
lean_dec(v_a_4006_);
lean_dec_ref(v_a_4005_);
return v_res_4010_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_4015_ = l_Lean_MessageData_ofFormat(v___x_4014_);
return v___x_4015_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_4018_, lean_object* v___x_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v___x_4025_; 
lean_inc(v___x_4019_);
lean_inc(v_mvarId_4018_);
v___x_4025_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4018_, v___x_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v___x_4026_; 
lean_dec_ref_known(v___x_4025_, 1);
lean_inc(v_mvarId_4018_);
v___x_4026_ = l_Lean_MVarId_getType(v_mvarId_4018_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref_known(v___x_4026_, 1);
v___x_4028_ = lean_box(0);
v___x_4029_ = l_Lean_Meta_synthInstance(v_a_4027_, v___x_4028_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4029_, 1);
lean_inc(v_mvarId_4018_);
v___x_4031_ = l_Lean_mkMVar(v_mvarId_4018_);
v___x_4032_ = l_Lean_Meta_isExprDefEq(v___x_4031_, v_a_4030_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4044_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4044_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4044_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
uint8_t v___x_4037_; 
v___x_4037_ = lean_unbox(v_a_4033_);
lean_dec(v_a_4033_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_del_object(v___x_4035_);
v___x_4038_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_4039_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4019_, v_mvarId_4018_, v___x_4038_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
return v___x_4039_;
}
else
{
lean_object* v___x_4040_; lean_object* v___x_4042_; 
lean_dec(v___x_4019_);
lean_dec(v_mvarId_4018_);
v___x_4040_ = lean_box(0);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4040_);
v___x_4042_ = v___x_4035_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4040_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v___x_4019_);
lean_dec(v_mvarId_4018_);
v_a_4045_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4032_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4032_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec(v___x_4019_);
lean_dec(v_mvarId_4018_);
v_a_4053_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4029_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4029_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec(v___x_4019_);
lean_dec(v_mvarId_4018_);
v_a_4061_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4026_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4026_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
else
{
lean_dec(v___x_4019_);
lean_dec(v_mvarId_4018_);
return v___x_4025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_4069_, lean_object* v___x_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_4069_, v___x_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v___x_4086_; lean_object* v___f_4087_; lean_object* v___x_4088_; 
v___x_4086_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_4080_);
v___f_4087_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4087_, 0, v_mvarId_4080_);
lean_closure_set(v___f_4087_, 1, v___x_4086_);
v___x_4088_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_4080_, v___f_4087_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_Lean_MVarId_inferInstance(v_mvarId_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx(lean_object* v_x_4096_){
_start:
{
switch(lean_obj_tag(v_x_4096_))
{
case 0:
{
lean_object* v___x_4097_; 
v___x_4097_ = lean_unsigned_to_nat(0u);
return v___x_4097_;
}
case 1:
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_unsigned_to_nat(1u);
return v___x_4098_;
}
default: 
{
lean_object* v___x_4099_; 
v___x_4099_ = lean_unsigned_to_nat(2u);
return v___x_4099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(lean_object* v_x_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Lean_Meta_TacticResultCNM_ctorIdx(v_x_4100_);
lean_dec(v_x_4100_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_4102_, lean_object* v_k_4103_){
_start:
{
if (lean_obj_tag(v_t_4102_) == 2)
{
lean_object* v_mvarId_4104_; lean_object* v___x_4105_; 
v_mvarId_4104_ = lean_ctor_get(v_t_4102_, 0);
lean_inc(v_mvarId_4104_);
lean_dec_ref_known(v_t_4102_, 1);
v___x_4105_ = lean_apply_1(v_k_4103_, v_mvarId_4104_);
return v___x_4105_;
}
else
{
lean_dec(v_t_4102_);
return v_k_4103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_4106_, lean_object* v_ctorIdx_4107_, lean_object* v_t_4108_, lean_object* v_h_4109_, lean_object* v_k_4110_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_4108_, v_k_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_4112_, lean_object* v_ctorIdx_4113_, lean_object* v_t_4114_, lean_object* v_h_4115_, lean_object* v_k_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_4112_, v_ctorIdx_4113_, v_t_4114_, v_h_4115_, v_k_4116_);
lean_dec(v_ctorIdx_4113_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_4118_, lean_object* v_closed_4119_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_4118_, v_closed_4119_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_4121_, lean_object* v_t_4122_, lean_object* v_h_4123_, lean_object* v_closed_4124_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_4122_, v_closed_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_4126_, lean_object* v_noChange_4127_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_4126_, v_noChange_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_4129_, lean_object* v_t_4130_, lean_object* v_h_4131_, lean_object* v_noChange_4132_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_4130_, v_noChange_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_4134_, lean_object* v_modified_4135_){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_4134_, v_modified_4135_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_4137_, lean_object* v_t_4138_, lean_object* v_h_4139_, lean_object* v_modified_4140_){
_start:
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_4138_, v_modified_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v___y_4152_; uint8_t v___y_4153_; lean_object* v_a_4158_; lean_object* v___x_4161_; 
v___x_4161_ = l_Lean_MVarId_getType(v_g_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v___x_4161_, 1);
v___x_4163_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_4164_ = lean_unsigned_to_nat(1u);
v___x_4165_ = lean_mk_empty_array_with_capacity(v___x_4164_);
v___x_4166_ = lean_array_push(v___x_4165_, v_a_4162_);
v___x_4167_ = l_Lean_Meta_mkAppM(v___x_4163_, v___x_4166_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4168_);
lean_dec_ref_known(v___x_4167_, 1);
v___x_4169_ = lean_box(0);
v___x_4170_ = l_Lean_Meta_synthInstance(v_a_4168_, v___x_4169_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4179_; 
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4179_ == 0)
{
lean_object* v_unused_4180_; 
v_unused_4180_ = lean_ctor_get(v___x_4170_, 0);
lean_dec(v_unused_4180_);
v___x_4172_ = v___x_4170_;
v_isShared_4173_ = v_isSharedCheck_4179_;
goto v_resetjp_4171_;
}
else
{
lean_dec(v___x_4170_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4179_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
uint8_t v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4177_; 
v___x_4174_ = 1;
v___x_4175_ = lean_box(v___x_4174_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 0, v___x_4175_);
v___x_4177_ = v___x_4172_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4175_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
else
{
lean_object* v_a_4181_; 
v_a_4181_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v___x_4170_, 1);
v_a_4158_ = v_a_4181_;
goto v___jp_4157_;
}
}
else
{
lean_object* v_a_4182_; 
v_a_4182_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4167_, 1);
v_a_4158_ = v_a_4182_;
goto v___jp_4157_;
}
}
else
{
lean_object* v_a_4183_; 
v_a_4183_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___x_4161_, 1);
v_a_4158_ = v_a_4183_;
goto v___jp_4157_;
}
v___jp_4151_:
{
if (v___y_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_dec_ref(v___y_4152_);
v___x_4154_ = lean_box(v___y_4153_);
v___x_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
return v___x_4155_;
}
else
{
lean_object* v___x_4156_; 
v___x_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4156_, 0, v___y_4152_);
return v___x_4156_;
}
}
v___jp_4157_:
{
uint8_t v___x_4159_; 
v___x_4159_ = l_Lean_Exception_isInterrupt(v_a_4158_);
if (v___x_4159_ == 0)
{
uint8_t v___x_4160_; 
lean_inc_ref(v_a_4158_);
v___x_4160_ = l_Lean_Exception_isRuntime(v_a_4158_);
v___y_4152_ = v_a_4158_;
v___y_4153_ = v___x_4160_;
goto v___jp_4151_;
}
else
{
v___y_4152_ = v_a_4158_;
v___y_4153_ = v___x_4159_;
goto v___jp_4151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_MVarId_isSubsingleton(v_g_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_4209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_4210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_4211_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_4208_, v___x_4209_, v___x_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_4213_;
}
}
lean_object* runtime_initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_debug_terminalTacticsAsSorry = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_debug_terminalTacticsAsSorry);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_tactic_skipAssignedInstances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_tactic_skipAssignedInstances);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Util(builtin);
}
#ifdef __cplusplus
}
#endif
